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
#include "libpawncpp.h"

#include <chrono>
#include <vector>
#include <amtl/am-string.h>

// C libraries.
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#if defined __WIN32__ || defined _WIN32 || defined _Windows
#	include <windows.h>
#	define FOREGROUND_WHITE (FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE) 
#elif defined __linux__ || defined __FreeBSD__ || defined __OpenBSD__ || defined DARWIN
#	include <sys/stat.h>
#	include <sys/types.h>
#endif

static int OutputMessage(unsigned short iForegroundFLags, const char *psOutputText, int iOutputLength)
{
	int iResult = 0;

#if defined __WIN32__ || defined _WIN32 || defined _Windows
	HANDLE hOutputSteam = GetStdHandle(STD_OUTPUT_HANDLE);

	if(hOutputSteam != NULL)
	{
		CONSOLE_SCREEN_BUFFER_INFO ConsoleScreenInfo;

		GetConsoleScreenBufferInfo(hOutputSteam, &ConsoleScreenInfo);
		SetConsoleTextAttribute(hOutputSteam, iForegroundFLags ? (iForegroundFLags | (ConsoleScreenInfo.wAttributes & ~FOREGROUND_WHITE)) : (ConsoleScreenInfo.wAttributes | FOREGROUND_WHITE));

		DWORD nNumberOfCharsWritten;

		// iResult = WriteConsole(hOutputSteam, sOutputText, iOutputLength, &nNumberOfCharsWritten, NULL);
		iResult = WriteFile(hOutputSteam, sOutputText, iOutputLength, &nNumberOfCharsWritten, NULL);
	}
#else
	iResult = fwrite(sOutputText, sizeof(char), iOutputLength, stdout);
	fflush(stdout);
#endif

	return iResult;
}

CompilerMessages::CompilerMessages()
{
	this->m_pMessagesVector = new std::vector<CompilerMessages::Message *>();
	this->m_iTotalStringLength = 0;
}

void CompilerMessages::AddMessage(const char *psMessage, int iLength, bool bIsCopy)
{
	if(iLength == -1)
	{
		iLength = static_cast<int>(strlen(sMessage));
	}

	CompilerMessages::Message *pMessageStruct = new CompilerMessages::Message();

	if((pMessageStruct->bTextIsCopy = bIsCopy))
	{
		char *sMessageCopy = new char[iLength];

		strncpy(sMessageCopy, sMessage, iLength);

		pMessageStruct->sText = sMessageCopy;
	}
	else
	{
		pMessageStruct->sText = sMessage;
	}

	pMessageStruct->iTextLength = iLength;

	this->m_pMessagesVector->push_back(pMessageStruct);
	this->m_iTotalStringLength += iLength;
}

int CompilerMessages::AddMessageFormat(const char *psFormatMessage, int iMaxLength, ...)
{
	char *sReadyMessage = new char[iMaxLength];

	va_list ArgsList;

	va_start(ArgsList, iMaxLength);

	int iMessageLength = static_cast<int>(ke::SafeVsprintf(sReadyMessage, static_cast<size_t>(iMaxLength), sFormatMessage, ArgsList));

	if(iMessageLength >> 31)		// Is minus.
	{
		perror(sReadyMessage);
	}

	va_end(ArgsList);

	CompilerMessages::Message *pMessageStruct = new CompilerMessages::Message();

	pMessageStruct->sText = sReadyMessage;
	pMessageStruct->iTextLength = iMessageLength;

	this->m_pMessagesVector->push_back(pMessageStruct);
	this->m_iTotalStringLength += iMessageLength;

	return iMessageLength;
}

int CompilerMessages::Print(unsigned short iForegroundFLags)
{
	std::vector<CompilerMessages::Message *> *pMessagesVector = this->m_pMessagesVector;

	int iResult = -1,
	    iSize = (int)pMessagesVector->size();

	if(iSize)
	{
		int iTextLength,
		    iOutputLength = this->m_iTotalStringLength;

		char *sOutputText = new char[iOutputLength];

		CompilerMessages::Message *pMessageBuffer;

		int j = 0;

		for(int i = 0; i != iSize && j < iOutputLength; i++)
		{
			// Read function args: L <- R.
			iTextLength = (pMessageBuffer = pMessagesVector->at(i))->iTextLength;

			memcpy(&sOutputText[j], pMessageBuffer->sText, iTextLength);

			j += iTextLength;
		}

		// // I faced a crash problem in this place. 
		// // Possible problems.
		// // memcpy() above, the string closing symbol will catch on.
		// sOutputText[j] = '\0';

		iResult = OutputMessage(iForegroundFLags, sOutputText, j);

		delete[] sOutputText;
	}

	return iResult;
}

CompilerMessages::~CompilerMessages()
{
	CompilerMessages::Message *pMessageStruct;

	std::vector<CompilerMessages::Message *> *pMessagesVector = this->m_pMessagesVector;

	for(int i = 0, iSize = static_cast<int>(pMessagesVector->size()); i != iSize; i++)
	{
		if((pMessageStruct = pMessagesVector->at(i))->bTextIsCopy)
		{
			delete[] pMessageStruct->sText;
		}

		delete pMessageStruct;
	}

	delete pMessagesVector;
	
	// And autodestructor with CompilerMessages::m_pMessagesVector member.
}

CompilerMessages *GetGlobalCompilerMessages()
{
	static CompilerMessages *pConsole = nullptr;

	if(!pConsole)
	{
		pConsole = new CompilerMessages();
	}

	return pConsole;
}

int PrintOnceMessage(unsigned short iForegroundFLags, const char *psMessage, int iLength)
{
	return OutputMessage(iForegroundFLags, sMessage, iLength != -1 ? iLength : static_cast<int>(strlen(sMessage)));
}

int PrintOnceMessageFormat(unsigned short iForegroundFLags, const char *psFormatMessage, int iMaxLength, ...)
{
	int iResult = -1;

	char *sOutputText = new char[iMaxLength];

	va_list ArgsList;

	va_start(ArgsList, iMaxLength);

	int iMessageLength = vsnprintf(sOutputText, iMaxLength, sFormatMessage, ArgsList);

	if(iMessageLength >> 31)		// Is minus.
	{
		perror(sOutputText);
	}

	va_end(ArgsList);

	OutputMessage(iForegroundFLags, sOutputText, iMessageLength);

	delete[] sOutputText;

	return iResult;
}

unsigned long long GetEpochTime()
{
	return std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::system_clock::now().time_since_epoch()).count();
}
