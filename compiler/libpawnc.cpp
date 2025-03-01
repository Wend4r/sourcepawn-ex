// vim: set sts=8 ts=2 sw=2 tw=99 et:
/*  LIBPAWNC.C
 *
 *  A "glue file" for building the Pawn compiler as a DLL or shared library.
 *
 *  Copyright (c) ITB CompuPhase, 2000-2006
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
#include "libpawnc.h"
#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "memfile.h"
#include "sc.h"

#if defined __linux__ || defined __FreeBSD__ || defined __OpenBSD__ || defined DARWIN
#	include <sys/stat.h>
#	include <sys/types.h>
#endif

/**
 * pc_printf()
 * Called for general purpose "console" output. This function prints general
 * purpose messages; errors go through pc_error(). The function is modelled
 * after printf().
 */
int
pc_printf(const char* message, ...)
{
	int ret;
	va_list argptr;

	va_start(argptr, message);

	ret = vprintf(message, argptr);

	va_end(argptr);

	return ret;
}

unsigned sc_total_errors = 0;

typedef struct src_file_s
{
	FILE* fp;         // Set if writing.
	char* buffer;     // IO buffer.
	char* pos;        // IO position.
	char* end;        // End of buffer.
	size_t maxlength; // Maximum length of the writable buffer.
} src_file_t;

/**
 * pc_opensrc()
 * Opens a source file (or include file) for reading. The "file" does not have
 * to be a physical file, one might compile from memory.
 *    filename    the name of the "file" to read from
 * Return:
 *    The function must return a pointer, which is used as a "magic cookie" to
 *    all I/O functions. When failing to open the file for reading, the
 *    function must return NULL.
 * Note:
 *    Several "source files" may be open at the same time. Specifically, one
 *    file can be open for reading and another for writing.
 */
void*
pc_opensrc(char* filename)
{
	FILE* fp = NULL;
	long length;
	src_file_t* src = NULL;

#if defined __linux__ || defined __FreeBSD__ || defined __OpenBSD__ || defined DARWIN
	struct stat fileInfo;

	if(stat(filename, &fileInfo) != 0)
	{
		return NULL;
	}

	if(S_ISDIR(fileInfo.st_mode))
	{
		return NULL;
	}
#endif

	if((fp = fopen(filename, "rb")) == NULL)
	{
		return NULL;
	}


	if(fseek(fp, 0, SEEK_END) == -1 || (length = ftell(fp)) == -1 || fseek(fp, 0, SEEK_SET) == -1 || (src = (src_file_t*)calloc(1, sizeof(src_file_t))) == NULL || (src->buffer = (char*)calloc(length, sizeof(char))) == NULL || fread(src->buffer, length, 1, fp) != 1)
	{
		goto err;
	}

	src->pos = src->buffer;
	src->end = src->buffer + length;

	fclose(fp);
	return src;

err:
	pc_closesrc(src);
	fclose(fp);

	return NULL;
}

/**
 * pc_createsrc()
 * Creates/overwrites a source file for writing. The "file" does not have
 * to be a physical file, one might compile from memory.
 *    filename    the name of the "file" to create
 * Return:
 *    The function must return a pointer which is used as a "magic cookie" to
 *    all I/O functions. When failing to open the file for reading, the
 *    function must return NULL.
 * Note:
 *    Several "source files" may be open at the same time. Specifically, one
 *    file can be open for reading and another for writing.
 */
void*
pc_createsrc(char* filename)
{
	src_file_t* src = (src_file_t*)calloc(1, sizeof(src_file_t));

	if(!src)
	{
		return NULL;
	}

	if(!(src->fp = fopen(filename, "wt")))
	{
		pc_closesrc(src);
		return NULL;
	}

	src->maxlength = 1024;
	if((src->buffer = (char*)calloc(1, src->maxlength)) == NULL) {
		pc_closesrc(src);
		return NULL;
	}

	src->pos = src->buffer;
	src->end = src->buffer + src->maxlength;
	return src;
}

/**
 * pc_closesrc()
 * Closes a source file (or include file). The "handle" parameter has the
 * value that pc_opensrc() returned in an earlier call.
 */
void
pc_closesrc(void* handle)
{
	src_file_t* src = (src_file_t*)handle;
	if(!src)
		return;
	if(src->fp) {
		fwrite(src->buffer, src->pos - src->buffer, 1, src->fp);
		fclose(src->fp);
	}
	free(src->buffer);
	free(src);
}

/**
 * pc_readsrc()
 * Reads a single line from the source file (or up to a maximum number of
 * characters if the line in the input file is too long).
 */
char*
pc_readsrc(void* handle, unsigned char* target, int maxchars)
{
	src_file_t* src = (src_file_t*)handle;

	char* outptr = (char*)target;
	char* outend = outptr + maxchars;

	assert(!src->fp);

	if(src->pos == src->end)
	{
		return NULL;
	}

	while(outptr < outend && src->pos < src->end)
	{
		char c = *src->pos++;

		*outptr++ = c;

		if(c == '\n')
		{
			break;
		}

		if(c == '\r')
		{
			// Handle CRLF.
			if(src->pos < src->end && *src->pos == '\n')
			{
				src->pos++;

				if(outptr < outend)
				{
					*outptr++ = '\n';
				}
			}
			else
			{
				// Replace with \n.
				*(outptr - 1) = '\n';
			}

			break;
		}
	}

	// Caller passes in a buffer of size >= maxchars+1.
	*outptr = '\0';

	return (char*)target;
}

/**
 * pc_writesrc()
 * Writes to to the source file. There is no automatic line ending; to end a
 * line, write a "\n".
 */
int
pc_writesrc(void* handle, unsigned char* source)
{
	char* str = (char*)source;

	size_t len = strlen(str);
	src_file_t* src = (src_file_t*)handle;

	assert(src->fp && src->maxlength);

	if(src->pos + len > src->end)
	{
		char* newbuf;

		size_t newmax = src->maxlength;
		size_t newlen = (src->pos - src->buffer) + len;

		while(newmax < newlen)
		{
			// Grow by 1.5X
			if((newmax += newmax + newmax / 2) < src->maxlength)
			{
				abort();
			}
		}

		if(!(newbuf = (char*)realloc(src->buffer, newmax)))
		{
			abort();
		}

		src->pos = newbuf + (src->pos - src->buffer);
		src->end = newbuf + newmax;
		src->buffer = newbuf;
		src->maxlength = newmax;
	}

	strcpy(src->pos, str);
	src->pos += len;

	return 0;
}

void*
pc_getpossrc(void* handle)
{
	src_file_t* src = (src_file_t*)handle;

	assert(!src->fp);

	return (void*)(ptrdiff_t)(src->pos - src->buffer);
}

/**
 * pc_resetsrc()
 * "position" may only hold a pointer that was previously obtained from
 * pc_getpossrc()
 */
void
pc_resetsrc(void* handle, void* position)
{
	src_file_t* src = (src_file_t*)handle;
	ptrdiff_t pos = (ptrdiff_t)position;

	assert(!src->fp);
	assert(pos >= 0 && src->buffer + pos <= src->end);

	src->pos = src->buffer + pos;
}

int
pc_eofsrc(void* handle)
{
	src_file_t* src = (src_file_t*)handle;

	assert(!src->fp);

	return src->pos == src->end;
}

/**
 * should return a pointer, which is used as a "magic cookie" to all I/O
 * functions; return NULL for failure
 */
memfile_t*
pc_openasm(char* filename)
{
	return memfile_creat(filename, 4096);
}

void
pc_closeasm(memfile_t* handle, int deletefile)
{
	if(handle)
	{
		if(!deletefile)
		{
			if(FILE* fp = fopen(handle->name.c_str(), "wb"))
			{
				fwrite(handle->base.get(), handle->usedoffs, 1, fp);
				fclose(fp);
			}
		}

		memfile_destroy(handle);
	}
}

void
pc_resetasm(memfile_t* handle)
{
	memfile_seek(handle, 0, SEEK_SET);
}

int
pc_writeasm(memfile_t* handle, const char* string)
{
	size_t bytes = strlen(string);

	return memfile_write(handle, string, bytes);
}
