// vim: set ts=8 sts=2 sw=2 tw=99 et:
//
//  Copyright (c) ITB CompuPhase, 1997-2006
//
//  This software is provided "as-is", without any express or implied warranty.
//  In no event will the authors be held liable for any damages arising from
//  the use of this software.
//
//  Permission is granted to anyone to use this software for any purpose,
//  including commercial applications, and to alter it and redistribute it
//  freely, subject to the following restrictions:
//
//  1.  The origin of this software must not be misrepresented; you must not
//      claim that you wrote the original software. If you use this software in
//      a product, an acknowledgment in the product documentation would be
//      appreciated but is not required.
//  2.  Altered source versions must be plainly marked as such, and must not be
//      misrepresented as being the original software.
//  3.  This notice may not be removed or altered from any source distribution.
#pragma once

#include <vector>

/**
 * Class for adding messages and quick single printing to STD output stream.
 */
class CompilerMessages
{
public:
	/**
	 * Constructor. 
	 * Initialize class members.
	 */
	CompilerMessages();

	/**
	 * Adds a message to the buffered vector with messages.
	 * 
	 * @param sFormatMessage      Message string.
	 * @param iLength             Message string length for copy. If -1 
	 *                            it will be calculated by strlen().
	 * @param bIsCopy             Is copy input message string.
	 */
	void AddMessage(const char *sMessage, int iLength = -1, bool bIsCopy = true);

	/**
	 * Adds a format message to the buffered vector with messages.
	 * 
	 * @param sFormatMessage      Message string for format.
	 * @param iMaxLength          Max size of formatted content.
	 * @param ...                 Format arguments.
	 * 
	 * @return                    Size after formatting.
	 */
	int AddMessageFormat(const char *sFormatMessage, int iMaxLength, ...);

	/**
	 * Fast prints a message from the message buffer.
	 * 
	 * @param iForegroundFLags    Text attributes (Only for Windows). 
	 *                            FOREGROUND_* and BACKGROUND_* flags.
	 * 
	 * @return                    Returns system call result or -1 if there are no messages 
	 *                            in the buffer and they were not output.
	 */
	int Print(unsigned short iForegroundFLags = 0);

	/**
	 * Deconstructor. 
	 * Clear allocated class data.
	 */
	~CompilerMessages();

private:
	struct Message
	{
		const char *sText;
		bool bTextIsCopy;
		int iTextLength;
	};

	std::vector<CompilerMessages::Message *> *m_pMessagesVector;
	int m_iTotalStringLength;
};

/**
 * Returns global pointer on buffer for Compiler output messages.
 */
CompilerMessages *GetGlobalCompilerMessages();

/**
 * Prints a message.
 * 
 * @param iForegroundFLags    Text attributes (Only for Windows). 
 *                            FOREGROUND_* flags.
 * @param sMessage            Message string.
 * @param iLength             Message string length. If -1 
 *                            it will be calculated by strlen().
 * 
 * @return                    Returns system call result.
 */
int PrintOnceMessage(unsigned short iForegroundFLags, const char *sMessage, int iLength = -1);

/**
 * Prints a format message.
 * 
 * @param iForegroundFLags    Text attributes (Only for Windows).
 *                            FOREGROUND_* flags.
 * @param sFormatMessage      Message string for format.
 * @param iMaxLength          Max size of formatted content.
 * @param ...                 Format arguments.
 * 
 * @return                    Returns system call.
 */
int PrintOnceMessageFormat(unsigned short iForegroundFLags, const char *sFormatMessage, int iMaxLength, ...);

/**
 * Returns the current epoch time in milliseconds.
 */
unsigned long long GetEpochTime();