/*  Pawn compiler - Staging buffer and optimizer
 *
 *  The staging buffer
 *  ------------------
 *  The staging buffer allows buffered output of generated code, deletion
 *  of redundant code, optimization by a tinkering process and reversing
 *  the ouput of evaluated expressions (which is used for the reversed
 *  evaluation of arguments in functions).
 *  Initially, stgwrite() writes to the file directly, but after a call to
 *  stgset(TRUE), output is redirected to the buffer. After a call to
 *  stgset(FALSE), stgwrite()'s output is directed to the file again. Thus
 *  only one routine is used for writing to the output, which can be
 *  buffered output or direct output.
 *
 *  staging buffer variables:   stgbuf  - the buffer
 *                              stgidx  - current index in the staging buffer
 *                              staging - if true, write to the staging buffer;
 *                                        if false, write to file directly.
 *
 * The peephole optimizer uses a dual "pipeline". The staging buffer (described
 * above) gets optimized for each expression or sub-expression in a function
 * call. The peephole optimizer is recursive, but it does not span multiple
 * sub-expressions. However, the data gets written to a second buffer that
 * behaves much like the staging buffer. This second buffer gathers all
 * optimized strings from the staging buffer for a complete expression. The
 * peephole optmizer then runs over this second buffer to find optimzations
 * across function parameter boundaries.
 *
 *
 *  Copyright (c) ITB CompuPhase, 1997-2006
 *
 *  This software is provided "as-is", without any express or implied warranty.
 *  In no event will the authors be held liable for any damages arising from
 *  the use of this software.
 *
 *  Permission is granted to anyone to use this software for any purpose,
 *  including commercial applications, and to alter it and redistribute it
 *  freely, subject to the following restrictions:
 *
 *  1.  The origin of this software must not be misrepresented; you must not
 *      claim that you wrote the original software. If you use this software in
 *      a product, an acknowledgment in the product documentation would be
 *      appreciated but is not required.
 *  2.  Altered source versions must be plainly marked as such, and must not be
 *      misrepresented as being the original software.
 *  3.  This notice may not be removed or altered from any source distribution.
 *
 *  Version: $Id$
 */
#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h> /* for atoi() */
#include <string.h>

#include <amtl/am-raii.h>

#include "emitter.h"
#include "errors.h"
#include "lexer.h"
#include "libpawnc.h"
#include "sc.h"
#include "scvars.h"

#if defined _MSC_VER
#	pragma warning(push)
#	pragma warning(disable : 4125) /* decimal digit terminates octal escape sequence */
#endif

#include "patterns.h"

#if defined _MSC_VER
#	pragma warning(pop)
#endif

static int stgstring(char *psStart, char *psEnd);
static void stgopt(char *psStart, char *psEnd, int (*funcOutPut)(char *sStr));

#define sSTG_GROW 512
#define sSTG_MAX 20480

static char* stgbuf = NULL;
static int stgmax = 0; /* current size of the staging buffer */

static char* stgpipe = NULL;
static int pipemax = 0; /* current size of the stage pipe, a second staging buffer */
static int pipeidx = 0;

#define CHECK_STGBUFFER(index)  \
	if((int)(index) >= stgmax) \
	grow_stgbuffer(&stgbuf, &stgmax, (index) + 1)
#define CHECK_STGPIPE(index)     \
	if((int)(index) >= pipemax) \
	grow_stgbuffer(&stgpipe, &pipemax, (index) + 1)

static void
grow_stgbuffer(char** buffer, int* curmax, int requiredsize)
{
	char* p;
	int clear = (*buffer == NULL); /* if previously none, empty buffer explicitly */

	assert(*curmax < requiredsize);
	/**
	 * if the staging buffer (holding intermediate code for one line) grows
	 * over a few kBytes, there is probably a run-away expression
	 */
	if(requiredsize > sSTG_MAX)
	{
		error(FATAL_ERROR_OOM);
	}

	*curmax = requiredsize + sSTG_GROW;

	if(*buffer != NULL)
	{
		p = (char*)realloc(*buffer, *curmax * sizeof(char));
	}
	else
	{
		p = (char*)malloc(*curmax * sizeof(char));
	}

	if(!p)
	{
		error(FATAL_ERROR_OOM);
	}

	*buffer = p;

	if(clear)
	{
		**buffer = '\0';
	}
}

void
stgbuffer_cleanup(void)
{
	if(stgbuf != NULL)
	{
		free(stgbuf);

		stgbuf = NULL;
		stgmax = 0;
	}

	if(stgpipe != NULL)
	{
		free(stgpipe);

		stgpipe = NULL;
		pipemax = 0;
		pipeidx = 0;
	}
}

/* the variables "stgidx" and "staging" are declared in "scvars.c" */

/*  stgmark
 *
 *  Copies a mark into the staging buffer. At this moment there are three
 *  possible marks:
 *     sSTARTREORDER    identifies the beginning of a series of expression
 *                      strings that must be written to the output file in
 *                      reordered order
 *    sENDREORDER       identifies the psEnd of 'reverse evaluation'
 *    sEXPRSTART + idx  only valid within a block that is evaluated in
 *                      reordered order, it identifies the psStart of an
 *                      expression; the "idx" value is the argument position
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (altered)
 *                     staging (referred to only)
 */
void
stgmark(char mark)
{
	if(staging)
	{
		CHECK_STGBUFFER(stgidx);
		stgbuf[stgidx++] = mark;
	}
}

static int
rebuffer(char* sStr)
{
	if(sc_status == statWRITE)
	{
		if(pipeidx >= 2 && stgpipe[pipeidx - 1] == '\0' && stgpipe[pipeidx - 2] != '\n')
		{
			pipeidx--;      /* overwrite last '\0' */
		}

		/* copy to staging buffer */
		while(*sStr)
		{
			CHECK_STGPIPE(pipeidx);
			stgpipe[pipeidx++] = *sStr++;
		}

		CHECK_STGPIPE(pipeidx);
		stgpipe[pipeidx++] = '\0';
	}

	return TRUE;
}

static int
filewrite(char* sStr)
{
	if(sc_status == statWRITE)
	{
		return pc_writeasm(outf, sStr);
	}

	return TRUE;
}

/*  stgwrite
 *
 *  Writes the string "st" to the staging buffer or to the output file. In the
 *  case of writing to the staging buffer, the terminating byte of zero is
 *  copied too, but... the optimizer can only work on complete lines (not on
 *  fractions of it. Therefore if the string is staged, if the last character
 *  written to the buffer is a '\0' and the previous-to-last is not a '\n',
 *  the string is concatenated to the last string in the buffer (the '\0' is
 *  overwritten). This also means an '\n' used in the middle of a string isn't
 *  recognized and could give wrong results with the optimizer.
 *  Even when writing to the output file directly, all strings are buffered
 *  until a whole line is complete.
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (altered)
 *                     staging (referred to only)
 */
void
stgwrite(const char *st)
{
	int st_len = static_cast<int>(strlen(st));

	if(staging)
	{
		assert(!stgidx ||stgbuf != NULL); /* staging buffer must be valid if there is (apparently) something in it */

		if(stgidx >= 2 && !stgbuf[stgidx - 1] && stgbuf[stgidx - 2] != '\n')
		{
			stgidx--; /* overwrite last '\0' */
		}

		CHECK_STGBUFFER(stgidx + st_len + 1);
		memcpy(stgbuf + stgidx, st, st_len + 1);

		stgidx += st_len + 1;
	}
	else
	{
		int iLength = stgbuf ? static_cast<int>(strlen(stgbuf)) : 0;

		CHECK_STGBUFFER(iLength + st_len + 1);
		memcpy(stgbuf + iLength, st, st_len + 1);

		iLength += st_len;

		if(iLength > 0 && stgbuf[iLength - 1] == '\n')
		{
			filewrite(stgbuf);
			stgbuf[0] = '\0';
		}
	}
}

/*  stgout
 *
 *  Writes the staging buffer to the output file via stgstring() (for
 *  reversing expressions in the buffer) and stgopt() (for optimizing). It
 *  resets "stgidx".
 *
 *  Global references: stgidx  (altered)
 *                     stgbuf  (referred to only)
 *                     staging (referred to only)
 */
void
stgout(int index)
{
	if(staging)
	{
		int reordered = 0;
		int idx;

		assert(pipeidx == 0);

		/* first pass: sub-expressions */
		if(sc_status == statWRITE)
		{
			reordered = stgstring(&stgbuf[index], &stgbuf[stgidx]);
		}

		stgidx = index;

		/* second pass: optimize the buffer created in the first pass */
		if(sc_status == statWRITE)
		{
			if(reordered)
			{
				stgopt(stgpipe, stgpipe + pipeidx, filewrite);
			}
			else
			{
				/* there is no sense in re-optimizing if the order of the sub-expressions
				* did not change; so output directly
				*/
				for(idx = 0; idx < pipeidx; idx += static_cast<int>(strlen(stgpipe + idx)) + 1)
				{
					filewrite(stgpipe + idx);
				}
			}
		}

		pipeidx = 0; /* reset second pipe */
	}
}

typedef struct
{
	char *psStart, *psEnd;
} argstack;

/*  stgstring
 *
 *  Analyses whether code strings should be output to the file as they appear
 *  in the staging buffer or whether portions of it should be re-ordered.
 *  Re-ordering takes place in function argument lists; Pawn passes arguments
 *  to functions from right to left. When arguments are "named" rather than
 *  positional, the order in the source stream is indeterminate.
 *  This function calls itself recursively in case it needs to re-order code
 *  strings, and it uses a private stack (or list) to mark the psStart and the
 *  end of expressions in their correct (reversed) order.
 *  In any case, stgstring() sends a block as large as possible to the
 *  optimizer stgopt().
 *
 *  In "reorder" mode, each set of code strings must psStart with the token
 *  sEXPRSTART, even the first. If the token sSTARTREORDER is represented
 *  by '[', sENDREORDER by ']' and sEXPRSTART by '|' the following applies:
 *     '[]...'     valid, but useless; no output
 *     '[|...]     valid, but useless; only one string
 *     '[|...|...] valid and usefull
 *     '[...|...]  invalid, first string doesn't psStart with '|'
 *     '[|...|]    invalid
 */
static int
stgstring(char *psStart, char *psEnd)
{
	char *sPtr;

	int nest, argc, arg;

	argstack *pArgStack;

	int reordered = 0;

	while(psStart < psEnd)
	{
		if(*psStart == sSTARTREORDER)
		{
			psStart++; /* skip token */

			/* allocate a argstack with SP_MAX_CALL_ARGUMENTS items */
			if(!(pArgStack = (argstack*)malloc(SP_MAX_CALL_ARGUMENTS * sizeof(argstack))))
			{
				error_once(103); /* insufficient memory */
			}

			reordered = 1;  /* mark that the expression is reordered */
			nest = 1;       /* nesting counter */
			argc = 0;       /* argument counter */
			arg = -1;       /* argument index; no valid argument yet */

			do
			{
				switch(*psStart)
				{
					case sSTARTREORDER:
					{
						nest++;
						psStart++;

						break;
					}

					case sENDREORDER:
					{
						nest--;
						psStart++;

						break;
					}

					default:
					{
						if((*psStart & sEXPRSTART) == sEXPRSTART)
						{
							if(nest == 1)
							{
								if(arg >= 0)
								{
									pArgStack[arg].psEnd = psStart - 1; /* finish previous argument */
								}

								arg = (unsigned char)*psStart - sEXPRSTART;
								pArgStack[arg].psStart = psStart + 1;

								if(arg >= argc)
								{
									argc = arg + 1;
								}
							}

							psStart++;
						}
						else
						{
							psStart += strlen(psStart) + 1;
						}
					}
				}
			}
			while(nest); /* enddo */

			if(arg >= 0)
			{
				pArgStack[arg].psEnd = psStart - 1; /* finish previous argument */
			}

			while(argc > 0)
			{
				argc--;
				stgstring(pArgStack[argc].psStart, pArgStack[argc].psEnd);
			}

			free(pArgStack);
		}
		else
		{
			sPtr = psStart;

			while(sPtr < psEnd && *sPtr != sSTARTREORDER)
			{
				sPtr += strlen(sPtr) + 1;
			}

			stgopt(psStart, sPtr, rebuffer);

			psStart = sPtr;
		}
	}

	return reordered;
}

/*  stgdel
 *
 *  Scraps code from the staging buffer by resetting "stgidx" to "index".
 *
 *  Global references: stgidx (altered)
 *                     staging (reffered to only)
 */
void
stgdel(int index, cell code_index)
{
	if(staging)
	{
		stgidx = index;
		code_idx = code_index;
	}
}

int
stgget(int* index, cell* code_index)
{
	if(staging)
	{
		*index = stgidx;
		*code_index = code_idx;
	}

	return staging;
}

/*  stgset
 *
 *  Sets staging on or off. If it's turned off, the staging buffer must be
 *  initialized to an empty string. If it's turned on, the routine makes sure
 *  the index ("stgidx") is set to 0 (it should already be 0).
 *
 *  Global references: staging  (altered)
 *                     stgidx   (altered)
 *                     stgbuf   (contents altered)
 */
void
stgset(int onoff)
{
	staging = onoff;

	if(staging)
	{
		assert(stgidx == 0);
		stgidx = 0;

		CHECK_STGBUFFER(stgidx);

		/**
		 * write any contents that may be put in the buffer by stgwrite()
		 * when "staging" was 0
		 */
		if(stgbuf[0])
		{
			filewrite(stgbuf);
		}
	}

	stgbuf[0] = '\0';
}

/* phopt_init
 * Initialize all sequence strings of the peehole optimizer. The strings
 * are embedded in the .EXE file in compressed format, here we expand
 * them (and allocate memory for the Sequences).
 */
static SEQUENCE *g_pSequences = sequences_cmp;

int
phopt_init(void)
{
	return TRUE;
}

int
phopt_cleanup(void)
{
	return FALSE;
}

#define MAX_OPT_VARS 5
#define MAX_OPT_CAT 5 /* max. values that are concatenated */
#if sNAMEMAX > (PAWN_CELL_SIZE / 4) * MAX_OPT_CAT
#	define MAX_ALIAS sNAMEMAX
#else
#	define MAX_ALIAS (PAWN_CELL_SIZE / 4) * MAX_OPT_CAT
#endif

static int
matchsequence(const char *psStart, const char *psEnd, const char *psPattern, char sSymbols[MAX_OPT_VARS][MAX_ALIAS + 1], int *iMatchLength)
{
	int iVar, i;
	char sStr[MAX_ALIAS + 1];

	const char *psStartOrg = psStart;

	cell iValue;
	char* sPtr;

	*iMatchLength = 0;

	for(iVar = 0; iVar < MAX_OPT_VARS; iVar++)
	{
		sSymbols[iVar][0] = '\0';
	}

	while(*psStart == '\t' || *psStart == ' ')
	{
		psStart++;
	}

	while(*psPattern)
	{
		if(psStart >= psEnd)
		{
			return FALSE;
		}

		switch(*psPattern)
		{
			case '%': /* new "symbol" */
			{
				psPattern++;

				assert(isdigit(*psPattern));
				iVar = atoi(psPattern) - 1;
				assert(iVar >= 0 && iVar < MAX_OPT_VARS);
				assert(*psStart == '-' || alphanum(*psStart));

				for(i = 0; psStart < psEnd && (*psStart == '-' || *psStart == '+' || alphanum(*psStart)); i++, psStart++)
				{
					assert(i <= MAX_ALIAS);
					sStr[i] = *psStart;
				}

				sStr[i] = '\0';

				if(sSymbols[iVar][0] != '\0')
				{
					if(strcmp(sSymbols[iVar], sStr))
					{
						return FALSE; /* sSymbols should be identical */
					}
				}
				else
				{
					strcpy(sSymbols[iVar], sStr);
				}

				break;
			}

			case '-':
			{
				iValue = -strtol(psPattern + 1, (char**)&psPattern, 16);
				sPtr = itoh((ucell)iValue);

				while(*sPtr)
				{
					if(tolower(*psStart) != tolower(*sPtr))
					{
						return FALSE;
					}

					psStart++;
					sPtr++;
				}

				psPattern--; /* there is an increment following at the psEnd of the loop */

				break;
			}

			case ' ':
			{
				if(*psStart != '\t' && *psStart != ' ')
				{
					return FALSE;
				}

				while(psStart < psEnd && (*psStart == '\t' || *psStart == ' '))
				{
					psStart++;
				}

				break;
			}

			case '!':
			{
				while(psStart < psEnd && (*psStart == '\t' || *psStart == ' '))
				{
					psStart++; /* skip trailing white space */
				}

				if(*psStart == ';')
				{
					while(psStart < psEnd && *psStart != '\n')
					{
						psStart++; /* skip trailing comment */
					}
				}

				if(*psStart != '\n')
				{
					return FALSE;
				}

				// assert(*(psStart + 1) == '\0');

				psStart += 2; /* skip '\n' and '\0' */

				if(psPattern[1])
				{
					while((psStart < psEnd && *psStart == '\t') || *psStart == ' ')
					{
						psStart++; /* skip leading white space of next instruction */
					}
				}

				break;
			}

			default:
			{
				if(tolower(*psStart) != tolower(*psPattern))
				{
					return FALSE;
				}

				psStart++;
			}
		}

		psPattern++;
	}

	*iMatchLength = (int)(psStart - psStartOrg);

	return TRUE;
}

static char*
replacesequence(const char *psPattern, char sSymbols[MAX_OPT_VARS][MAX_ALIAS + 1], int *iReplaceLength)
{
	const char *psLinePtr;
	int iVar;
	char* buffer;

	/**
	 * Сalculate the length of the new buffer
	 * this is the length of the psPattern plus the length of all sSymbols (note
	 * that the same symbol may occur multiple times in the psPattern) plus
	 * line endings and startings ('\t' to psStart a line and '\n\0' to psEnd one)
	 */
	assert(iReplaceLength != NULL);

	*iReplaceLength = 0;
	psLinePtr = psPattern;

	while(*psLinePtr)
	{
		switch(*psLinePtr)
		{
			case '%':
			{
				psLinePtr++; /* skip '%' */

				assert(isdigit(*psLinePtr));

				iVar = atoi(psLinePtr) - 1;

				assert(iVar >= 0 && iVar < MAX_OPT_VARS);
				assert(sSymbols[iVar][0] != '\0'); /* variable should be defined */

				*iReplaceLength += static_cast<int>(strlen(sSymbols[iVar]));

				break;
			}

			case '!':
			{
				*iReplaceLength += 3; /* '\t', '\n' & '\0' */

				break;
			}

			default:
			{
				*iReplaceLength += 1;
			}
		}

		psLinePtr++;
	}

	/* allocate a buffer to replace the sequence in */
	if(!(buffer = (char*)malloc(*iReplaceLength)))
	{
		error_once(103);
		return NULL;
	}

	/* replace the psPattern into this temporary buffer */
	char* sPtr = buffer;

	*sPtr++ = '\t'; /* the "replace" patterns do not have tabs */

	while(*psPattern)
	{
		assert((int)(sPtr - buffer) < *iReplaceLength);

		switch(*psPattern)
		{
			case '%':
			{
				/* write out the symbol */
				psPattern++;

				assert(isdigit(*psPattern));

				iVar = atoi(psPattern) - 1;

				assert(iVar >= 0 && iVar < MAX_OPT_VARS);
				assert(sSymbols[iVar][0] != '\0'); /* variable should be defined */

				strcpy(sPtr, sSymbols[iVar]);
				sPtr += strlen(sSymbols[iVar]);

				break;
			}

			case '!':
			{
				/* finish the line, optionally psStart the next line with an indent */
				*sPtr++ = '\n';
				*sPtr++ = '\0';

				if(*(psPattern + 1))
				{
					*sPtr++ = '\t';
				}

				break;
			}

			default:
			{
				*sPtr++ = *psPattern;
			}
		}

		psPattern++;
	}

	assert((int)(sPtr - buffer) == *iReplaceLength);

	return buffer;
}

static void
strreplace(char* dest, char* replace, int sub_length, int iReplaceLength, int dest_length)
{
	int iOffset = sub_length - iReplaceLength;

	/* delete a section */
	if(iOffset > 0)
	{
		memmove(dest, dest + iOffset, dest_length - iOffset);
		memset(dest + dest_length - iOffset, 0xCC, iOffset); /* not needed, but for cleanlyness */
	}
	else if(iOffset < 0) /* insert a section */
	{
		memmove(dest - iOffset, dest, dest_length);
	}

	memcpy(dest, replace, iReplaceLength);
}

/*  stgopt
 *
 *  Optimizes the staging buffer by checking for series of instructions that
 *  can be coded more compact. The routine expects the lines in the staging
 *  buffer to be separated with '\n' and '\0' characters.
 *
 *  The longest Sequence should probably be checked first.
 */

static void
stgopt(char* psStart, char* psEnd, int (*funcOutPut)(char* sStr))
{
	char sSymbols[MAX_OPT_VARS][MAX_ALIAS + 1];

	char *sDebut = psStart; /* save original psStart of the buffer */

	// printf("sDebut = %s\n", sDebut);

	// assert(s_pSequences != NULL);

	/* do not match anything if debug-level is maximum */

	// printf("stgopt(): pc_optimize = %i\n", pc_optimize);

	if(pc_optimize > sOPTIMIZE_NONE && sc_status == statWRITE)
	{
		int iSaveSize, seq, iMatchLength, iReplaceLength, matches;

		do
		{
			matches = 0;
			psStart = sDebut;

			while(psStart < psEnd)
			{
				seq = 0;

				while(g_pSequences[seq].psFind != NULL)
				{
					assert(seq >= 0);

					if(g_pSequences[seq].iOptimizeLevel <= pc_optimize)
					{
						if(!*g_pSequences[seq].psFind)
						{
							if(pc_optimize == sOPTIMIZE_LEVEL1)
							{
								break; /* don't look further */
							}
							else
							{
								seq++; /* continue with next string */

								continue;
							}
						}
						if(matchsequence(psStart, psEnd, g_pSequences[seq].psFind, sSymbols, &iMatchLength))
						{
							char *sReplace = replacesequence(g_pSequences[seq].psReplace, sSymbols, &iReplaceLength);

							/* If the replacement is bigger than the original section, we may need
							* to "grow" the staging buffer. This is quite complex, due to the
							* re-ordering of expressions that can also happen in the staging
							* buffer. In addition, it should not happen: the peephole optimizer
							* must replace g_pSequences with *shorter* g_pSequences, not longer ones.
							* So, I simply forbid g_pSequences that are longer than the ones they
							* are meant to replace.
							*/
							assert(iMatchLength >= iReplaceLength);

							if(iMatchLength >= iReplaceLength)
							{
								strreplace(psStart, sReplace, iMatchLength, iReplaceLength, (int)(psEnd - psStart));

								psEnd -= iMatchLength - iReplaceLength;

								free(sReplace);

								opt_code_count += iSaveSize = g_pSequences[seq].iSaveSize;
								code_idx -= iSaveSize;

								seq = 0; /* restart search for matches */
								matches++;

								continue;
							}
							else
							{
								/* actually, we should never get here (iMatchLength<iReplaceLength) */
								assert(0);
							}
						}
					}

					// assert(g_pSequences[seq].psFind == NULL || (*g_pSequences[seq].psFind == '\0' && pc_optimize == sOPTIMIZE_DEFAULT));

					seq++;
				}

				psStart += strlen(psStart) + 1; /* to next string */
			} /* while(psStart<psEnd) */
		}
		while(matches > 0);
	}
	/* if(pc_optimize>sOPTIMIZE_NONE && sc_status==statWRITE) */

	for(psStart = sDebut; psStart < psEnd; psStart += strlen(psStart) + 1)
	{
		funcOutPut(psStart);
	}

	// if(pc_optimize == sOPTIMIZE_LEVEL3)
	// {
	// 	ke::SaveAndSet<int> disable_phopt(&pc_optimize, sOPTIMIZE_LEVEL2);

	// 	stgopt(sDebut, psEnd, funcOutPut);
	// }
}

#undef SCPACK_TABLE
