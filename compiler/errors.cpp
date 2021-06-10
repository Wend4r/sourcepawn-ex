// vim: set ts=8 sts=4 sw=4 tw=99 et:
/*  Pawn compiler - Error message system
 *  In fact a very simple system, using only 'panic mode'.
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
 *  Version: $Id$F
 */
#include <assert.h>
#if defined __WIN32__ || defined _WIN32 || defined __MSDOS__
#	include <io.h>
#	include <windows.h>
#endif
#if defined __linux__ || defined __GNUC__
#	include <unistd.h>
#endif
#include <stdarg.h> /* ANSI standardized variable argument list functions */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "errors.h"
#include "lexer.h"
#include "libpawnc.h"
#include "libpawncpp.h"
#include "sc.h"
#include "sclist.h"
#include "scvars.h"

#if defined _MSC_VER
#	pragma warning(push)
#	pragma warning(disable : 4125) /* decimal digit terminates octal escape sequence */
#endif

#include "messages.h"

#if defined _MSC_VER
#	pragma warning(pop)
#endif

CompilerMessages g_ErrorMessages, g_WarningMessages;

#define NUM_WARNINGS (int)(sizeof warnmsg / sizeof warnmsg[0])

static unsigned char warndisable[(NUM_WARNINGS + 7) / 8]; /* 8 flags in a char */

static int errflag;
static AutoErrorPos* sPosOverride = nullptr;

AutoErrorPos::AutoErrorPos(const token_pos_t& pos)
  : pos_(pos),
    prev_(sPosOverride)
{
	sPosOverride = this;
}

AutoErrorPos::~AutoErrorPos()
{
	assert(sPosOverride == this);
	sPosOverride = prev_;
}


/**
 * error
 *
 *  Outputs an error message (note: msg is passed optionally).
 *  If an error is found, the variable "errflag" is set and subsequent
 *  errors are ignored until lex() finds a semicolumn or a keyword
 *  (lex() resets "errflag" in that case).
 *
 *  Global references: inpfname   (reffered to only)
 *                     fline      (reffered to only)
 *                     fcurrent   (reffered to only)
 *                     errflag    (altered)
 */
void
error(int iErrorNumber, ...)
{
	if(sPosOverride)
	{
		va_list ap;

		va_start(ap, iErrorNumber);
		error_va(sPosOverride->pos(), iErrorNumber, ap);
		va_end(ap);

		return;
	}

	va_list ap;

	va_start(ap, iErrorNumber);

	ErrorReport Report = ErrorReport::infer_va(iErrorNumber, ap);

	va_end(ap);

	report_error(&Report);
}

void
error(const token_pos_t &where, int number, ...)
{
	va_list ap;

	va_start(ap, number);

	ErrorReport report = ErrorReport::create_va(number, where.file, where.line, where.col, ap);

	va_end(ap);

	report.lineno = where.line;
	report_error(&report);
}

void
error_once(int iErrorNumber)
{
	if(sPosOverride)
	{
		error_va(sPosOverride->pos(), iErrorNumber, nullptr);
	}
	else
	{
		ErrorReport Report = ErrorReport::infer_va(iErrorNumber, nullptr);

		report_error(&Report);
	}
}

void
error_va(const token_pos_t &where, int number, va_list ap)
{
	ErrorReport report = ErrorReport::create_va(number, where.file, where.line, where.col, ap);

	report.lineno = where.line;
	report_error(&report);
}

void
error(symbol* sym, int number, ...)
{
	va_list ap;

	va_start(ap, number);

	ErrorReport report = ErrorReport::create_va(number, sym->fnumber, sym->lnumber, sym->colnumber, ap);

	va_end(ap);

	report_error(&report);
}

static void
abort_compiler()
{
	if(!errfname[0])
	{
		GetGlobalCompilerMessages()->AddMessage("\nCompilation aborted.", -1, false);
	}

	if(outf != NULL)
	{
		pc_closeasm(outf, TRUE);
		outf = NULL;
	}

	longjmp(errbuf, 2); /* fatal error, quit */
}

ErrorReport
ErrorReport::create_va(int iErrorNumber, int fileno, int lineno, int colno, va_list ap)
{
	ErrorReport report;

	report.number = iErrorNumber;
	report.fileno = fileno;
	report.lineno = lineno;
	report.colno = colno;

	if(report.fileno >= 0)
	{
		report.filename = get_inputfile(report.fileno);
	}
	else
	{
		report.filename = inpfname;
	}

	if(iErrorNumber < FIRST_FATAL_ERROR || (iErrorNumber >= 200 && sc_warnings_are_errors))
	{
		report.type = ErrorType::Error;
	}
	else if(iErrorNumber < 200)
	{
		report.type = ErrorType::Fatal;
	}
	else
	{
		report.type = ErrorType::Warning;
	}

	/* also check for disabled warnings */
	if(report.type == ErrorType::Warning)
	{
		int index = (report.number - 200) / 8;
		int mask = 1 << ((report.number - 200) % 8);

		if(warndisable[index] & mask)
		{
			report.type = ErrorType::Suppressed;
		}
	}

	const char* prefix = "";

	switch(report.type)
	{
		case ErrorType::AnalysisError:
		{
			prefix = "analysis error";
			break;
		}

		case ErrorType::Error:
		{
			prefix = "error";
			break;
		}

		case ErrorType::Fatal:
		{
			prefix = "fatal error";
			break;
		}

		case ErrorType::Warning:
		case ErrorType::Suppressed:
		{
			prefix = "warning";
			break;
		}
	}

	const char* format = nullptr;

	if(report.number < FIRST_FATAL_ERROR)
	{
		format = errmsg[report.number - 1];
	}
	else if(report.number < 200)
	{
		format = fatalmsg[report.number - FIRST_FATAL_ERROR];
	}
	else
	{
		format = warnmsg[report.number - 200];
	}

	char msg[1024];

	ke::SafeVsprintf(msg, sizeof(msg), format, ap);

	char full[2048];

	ke::SafeSprintf(full, sizeof(full), "%s(%d) : %s %03d: %s", report.filename, report.lineno, prefix, report.number, msg);		// Is MS style (Old).

	/**
	 * "pattern":
	 * {
	 * 	"regexp": "^(.*):(\\d+):(\\d+):\\s+(warning|error):\\s+(.*)$",
	 * 	"file": 1,
	 * 	"line": 2,
	 * 	"column": 3,
	 * 	"severity": 4,
	 * 	"message": 5
	 * }
	 */
	// ke::SafeSprintf(full, sizeof(full), "%s:%d:%d: %s %03d: %s", report.filename, report.lineno, report.colno + 1 /* Started by 0 */, prefix, report.number, msg);

	report.message = full;

	return report;
}

ErrorReport
ErrorReport::infer_va(int number, va_list ap)
{
	return create_va(number, -1, fline, pline[0] ? (int)(g_sLinePtr - pline) : -1, ap);
}

void
report_error(ErrorReport *pReport)
{
	static int lastline, errorcount;
	static short lastfile;

	/* errflag is reset on each semicolon.
	 * In a two-pass compiler, an error should not be reported twice. Therefore
	 * the error reporting is enabled only in the second pass (and only when
	 * actually producing output). Fatal errors may never be ignored.
	 */
	if(pReport->type != ErrorType::Fatal)
	{
		if(errflag)
		{
			return;
		}

		if(sc_status != statWRITE && !sc_err_status)
		{
			return;
		}
	}

	switch(pReport->type)
	{
		case ErrorType::Suppressed:
		{
			return;
		}

		case ErrorType::Warning:
		{
			warnnum++;
			break;
		}

		case ErrorType::Error:
		case ErrorType::Fatal:
		{
			errnum++;
			sc_total_errors++;
			errflag = TRUE;

			break;
		}
	}

	FILE* fp = nullptr;

	if(errfname[0])
	{
		fp = fopen(errfname, "a");
	}

	std::string sError = pReport->message;

	int iErrorLength = static_cast<int>(sError.size());

	if(fp)
	{
		fwrite(sError.c_str(), sizeof(char), iErrorLength, fp);
		fflush(fp);
		fclose(fp);
	}
	else
	{
		if(pReport->type == ErrorType::Warning)
		{
			g_WarningMessages.AddMessage(sError.c_str(), iErrorLength, true);
		}
		else
		{
			g_ErrorMessages.AddMessage(sError.c_str(), iErrorLength, true);
		}
	}

	if(pReport->type == ErrorType::Fatal || errnum > 25)
	{
		abort_compiler();

		return;
	}

	// Count messages per line, reset if not the same line.
	if(lastline != pReport->lineno || pReport->fileno != lastfile)
	{
		errorcount = 0;
	}

	lastline = pReport->lineno;
	lastfile = pReport->fileno;

	if(pReport->type != ErrorType::Warning)
	{
		errorcount++;
	}

	if(errorcount >= 3)
	{
		error(FATAL_ERROR_OVERWHELMED_BY_BAD);
	}
}

void
errorset(int code, int line)
{
	switch(code)
	{
		case sRESET:
		{
			errflag = FALSE; /* start reporting errors */
			break;
		}
		case sFORCESET:
		{
			errflag = TRUE; /* stop reporting errors */
			break;
		}
	}
}

int print_errors()
{
	int iErrorsOutput;

#if defined __WIN32__ || defined _WIN32  || defined _Windows
	iErrorsOutput = g_ErrorMessages.Print(FOREGROUND_RED);

	g_WarningMessages.Print(FOREGROUND_RED | FOREGROUND_GREEN);
#else
	iErrorsOutput = g_ErrorMessages.Print();

	g_WarningMessages.Print();
#endif

	return iErrorsOutput;
}

/* sc_enablewarning()
 * Enables or disables a warning (errors cannot be disabled).
 * Initially all warnings are enabled. The compiler does this by setting bits
 * for the *disabled* warnings and relying on the array to be zero-initialized.
 *
 * Parameter enable can be:
 *  o  0 for disable
 *  o  1 for enable
 *  o  2 for toggle
 */
int
pc_enablewarning(int number, int enable)
{
	int index;
	unsigned char mask;

	if(number < 200)
		return FALSE; /* errors and fatal errors cannot be disabled */
	number -= 200;
	if(number >= NUM_WARNINGS)
		return FALSE;

	index = number / 8;
	mask = (unsigned char)(1 << (number % 8));
	switch(enable) {
		case 0:
			warndisable[index] |= mask;
			break;
		case 1:
			warndisable[index] &= (unsigned char)~mask;
			break;
		case 2:
			warndisable[index] ^= mask;
			break;
	}

	return TRUE;
}

#undef SCPACK_TABLE
