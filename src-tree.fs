\ ==============================================================================
\
\              src-tree - the text input stream module in the ffl
\
\               Copyright (C) 2006-2007  Dick van Oudheusden
\  
\ This library is free software; you can redistribute it and/or
\ modify it under the terms of the GNU Lesser General Public
\ License as published by the Free Software Foundation; either
\ version 3 of the License, or (at your option) any later version.
\
\ This library is distributed in the hope that it will be useful,
\ but WITHOUT ANY WARRANTY; without even the implied warranty of
\ MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
\ Lesser General Public License for more details.
\
\ You should have received a copy of the GNU Lesser General Public
\ License along with this library; if not, write to the Free
\ Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
\
\ ==============================================================================
\ 
\  $Date: 2008-02-21 20:31:19 $ $Revision: 1.21 $
\
\ ==============================================================================

include ffl/snl.fs
include ffl/sni.fs
include ffl/snn.fs
include ffl/tis.fs
include ffl/str.fs
include ffl/chs.fs
include ffl/enm.fs
include ffl/bct.fs
include ffl/bci.fs

( src-tree = Дерево исходного кода )

\ Этот файл src-tree-03.00.fs сделан из предыдущего src-tree-02.00.fs
\ 14/01/19
\ Здесь все работает
\ -- строится список кода
\ -- список имен определений слов
\ -- для каждого слова сохраняется его тело
\ Следующая версия. В следующей версии надо сделать
\ составление списков определений слов, в которые входит
\ данное слово


\ Этот файл src-tree-01.00.fs сделан из предыдущего src-tree-00.00.fs
\ здесь я пытаюсь решить проблему конца строки.
\ т.к. разделитель по пробелам работает корректно только когда нет
\ символа конца строки. В противном случае он объединяет несколько строк
\ Вариант 1. Сделать счмтыватель файла по строчный, тогда автоматически
\ конец строки не будет присутствовать в счтанной строке
\ и остается только добавить к концу строки символ пробела, чтобы
\ разделитель по пробелам работал корректно на концах строк.

\ ==============================================================================
\ Settings
\ ==============================================================================

char / constant directory-separator        \ Directory separator
char . constant extension-separator        \ File extension separator

1022   constant source-line-size           \ Maximum size of the source line

\ ==============================================================================
\ Constants
\ ==============================================================================

str-create fsdocgen-version  s" 0.1.0" fsdocgen-version str-set

\ ==============================================================================
\ The documented item
\ ==============================================================================

\ ------------------------------------------------------------------------------
\ Data structure
\ ------------------------------------------------------------------------------

begin-enumeration
  enum: begin.enumeration
  enum: enum.enumeration
  enum: end.enumeration
  enum: begin.structure
  enum: field.structure
  enum: +field.structure
  enum: field:.structure
  enum: ffield:.structure
  enum: end.structure
  enum: begin.def
  enum: name.def
  enum: body.def
  enum: end.def
  enum: exec.statment
  enum: begin.comment.br
  enum: end.comment.br
enum: begin.comment.backslash
enum: end.line
enum: enumeration.type
enum: structure.type
enum: def.type
enum: exec.type
enum: char.def
enum: char.def.end
  enum: lex.#num
end-enumeration

\ ------------------------------------------------------------------------------------
\ Construction structures
\ ------------------------------------------------------------------------------------
begin-structure pnt%
    snn% +field pnt>snn
    field: pnt>def              \ Указатель на def
end-structure

begin-structure def%
    snn% +field def>snn
    field: def>id                \ идентификатор слова
    field: def>type            \ тип определения
    str% +field def>name \ имя определения слова
    str% +field def>body \ полное определение слова
    snl% +field def>pnts  \ список указателей на слова, pnt pnt ... pnt
                                      \  в которых встречается данное слово
    sni% +field def>pnts-iter
end-structure

( Для того чтобы учитывать имя файла, в котором находятся данные определения, можно ввести еще один уравень. )
begin-structure prt% \ project
    snn% +field prt>snn
    str% +field prt>filename \ имя файла относительно route
    str% +field prt>route      \ корень проекта или родительская папка проекта
    snl% +field prt>defs        \ Список определений в этом файле def def ... def
    sni% +field prt>defs-iter
end-structure

\ Stack
begin-structure nd%
    snn% +field nd>snn
    field: nd>val
end-structure

\ ------------------------------------------------------------------------------
\ allocator
\ ------------------------------------------------------------------------------
: pnt-new ( -- pnt = Allocant a new pnt item )
    pnt% allocate throw
    >r
    r@ pnt>snn snn-init
    0 r@ pnt>def !
    r>
;

: def-new ( -- def = Allocate a new def item )
    def% allocate throw
    >r
    r@ def>snn snn-init
    r@ def>pnts dup snl-init
    r@ def>pnts-iter sni-init
    r@ def>name str-init
    r@ def>body str-init
    r@ def>id 0!
    r@ def>type 0!
    r>
;

: prt-new ( -- prt = Allocate a new prt item )
    prt% allocate throw
    >r
    r@ prt>snn snn-init
    r@ prt>defs dup snl-init
    r@ prt>defs-iter sni-init
    r@ prt>filename str-init
    r@ prt>route str-init    
    r>
;

\ Stack
: nd-new ( n -- nd )
    nd% allocate throw
    >r
    r@ nd>val !
    r>
;

\ ------------------------------------------------------------------------------
\ Deallocator
\ ------------------------------------------------------------------------------

: pnt-free ( pnt -- = Free the pnt )
    ." pnt free" 
    ?free throw
;

: def-free ( def -- = Free the def )
    \ ." def free" 
    >r
    ['] pnt-free
    r@ def>pnts snl-(free)
    r@ def>name str-(free)
    r@ def>body str-(free)
    r> free throw
;

: prt-free ( prt -- = Free the prt variable )
    \ ." prt free" 
    >r
    ['] def-free
    r@ prt>defs snl-(free)
    r@ prt>filename str-(free)
    r@ prt>route str-(free)
    r> free throw
;
\ use
\ prt-var @ prt-free
\ ok!!!!!!

: nd-free ( stack -- )
    >r
    r@ snl-(free)
    r> free throw
;

snl-new value stack
lex.#num nd-new stack snl-push

snl-new value prt-var 
prt-new prt-var snl-append

( Input stream structure )
variable y0
lex.#num y0 !

bct-new value src-lex-table
\ bct-create src-lex-table

: lex-compare  ( str str - n = Compare the two mountain names )
  str^ccompare
;

' lex-compare src-lex-table bct-compare!

\ Create a text input stream on the heap

tis-new value tis2

begin.enumeration str-new dup s" begin-enumeration" rot str-set src-lex-table bct-insert
enum.enumeration str-new dup s" enum:" rot str-set src-lex-table bct-insert
end.enumeration str-new dup s" end-enumeration" rot str-set src-lex-table bct-insert
begin.structure str-new dup s" begin-structure" rot str-set src-lex-table bct-insert
end.structure str-new dup s" end-structure" rot str-set src-lex-table bct-insert
+field.structure str-new dup s" +field" rot str-set src-lex-table bct-insert
field:.structure str-new dup s" field:" rot str-set src-lex-table bct-insert
ffield:.structure str-new dup s" ffield:" rot str-set src-lex-table bct-insert

begin.def str-new dup s" :" rot str-set src-lex-table bct-insert
end.def str-new dup s" ;" rot str-set src-lex-table bct-insert

begin.comment.backslash str-new dup s" \" rot str-set src-lex-table bct-insert
begin.comment.br str-new dup s" (" rot str-set src-lex-table bct-insert
end.comment.br str-new dup s" )" rot str-set src-lex-table bct-insert
end.line str-new dup s" end-line" rot str-set src-lex-table bct-insert

char.def str-new dup s" [char]" rot str-set src-lex-table bct-insert

\ Setup the reader callback word

: tis-reader ( fileid -- c-addr u | 0 )
  pad 64 rot read-file throw
  dup IF
    pad swap
  THEN
;

( Special words )
str-new value str-temp

: lex-emit ( x x -- )
    str-get type ."  --> " . cr
;
\ ' mount-emit mountains bct-execute
' lex-emit src-lex-table bct-execute

\ ------------------------------------------------------------------------------
\ Parse 
\ ------------------------------------------------------------------------------
: state-set ( state -- )
    y0 !
;

: get-state@ ( -- state )
    y0 @
;

: src-new-def ( prt -- )
    ." src new def" .s cr
    >r
    def-new r@ prt>defs snl-append
    r> drop
;

: src-name-def ( str def -- )
    ." src name def" .s cr
    >r
    str-get r@ def>name  str-set
    r> drop
;

: src-body-def ( str def -- )
    ." src body def" .s cr
    >r
    r@ def>body str-empty? IF
	." str empty" 
	str-get r@ def>body str-set
    ELSE
	." else str empty"
	chr.sp r@ def>body str-append-char
	str-get r@ def>body str-append-string
    THEN
    r> drop
;

: parse-char-def ( -- )
    get-state@ nd-new stack snl-push
    char.def state-set
    
;

: parse-end-char-def ( -- )
    stack snl-tos nd>val @ state-set
    stack snl-pop snn-free
;

\ ------------------------------------------------------------------------------
\ Lex
\ ------------------------------------------------------------------------------

: ele-name ( c-addr u -- )
    (
    Определяет токен
    )
    \ ." begin ele name: " \ .s cr
    str-temp str-set \ str-temp str-get type ." ^"
    str-temp src-lex-table bct-get  \ ." ele name: " .s cr
    IF
	CASE
	    begin.def OF ." BEGIN DEF: " prt-var snl-last@ src-new-def
		name.def state-set  ENDOF
	    end.def OF ." END DEF." end.def state-set ENDOF
	    begin.comment.backslash OF ." BEGIN COMMENT BACKSLASH."
		tis2 tis-read-all dup 0<> IF type cr ELSE drop THEN
		
	    ENDOF
	    begin.comment.br OF ." BEGIN COMMENT BR"
		get-state@ char.def <> IF
		    get-state@ nd-new stack snl-push begin.comment.br state-set get-state@ .
		ELSE
		    str-temp prt-var snl-last@ prt>defs snl-last@ src-body-def
		    parse-end-char-def
		ENDIF
	    ENDOF
	    end.comment.br OF ." END COMMENT BR."
		get-state@ char.def <> IF
		    stack snl-tos nd>val @ state-set stack snl-pop snn-free get-state@ .
		ELSE
		    str-temp prt-var snl-last@ prt>defs snl-last@ src-body-def
		    parse-end-char-def
		ENDIF
	    ENDOF
	    char.def OF ." BEGIN CHAR DEF"
		str-temp prt-var snl-last@ prt>defs snl-last@ src-body-def
		parse-char-def ENDOF
	    begin.enumeration OF ." BEGIN ENUM" ENDOF
	    enum.enumeration OF ." ENUM" ENDOF
	    end.enumeration OF ." END ENUM" ENDOF
	    begin.structure OF ." BEGIN STRUCT" ENDOF
	    end.structure OF ." END STRUCT" ENDOF
	    +field.structure OF ." +FIELD:" ENDOF
	    field:.structure OF ." FIELD:" ENDOF
	    ffield:.structure OF ." FFIELD" ENDOF
	    end.line OF ." END LINE"
	    ENDOF
	ENDCASE
	cr \ ." ele name endcase:" \ .s
    ELSE
	y0 @
	CASE
	    name.def OF str-temp prt-var snl-last@ prt>defs snl-last@ src-name-def
		body.def state-set ENDOF
	    body.def  OF str-temp prt-var snl-last@ prt>defs snl-last@ src-body-def ENDOF
	    char.def OF str-temp prt-var snl-last@ prt>defs snl-last@ src-body-def
	    parse-end-char-def ENDOF
	ENDCASE
    THEN
    str-temp str-clear
;

\ ------------------------------------------------------------------------------
\ Read a line from the source file
\ ------------------------------------------------------------------------------

: open-input-file  ( str -- fileid = Open the input file, throws any errors )
    str-get r/o open-file throw
;

: start-reading-source  ( str -- fileid fileid = Start reading a source file resulting in an input fileid and output fileid )
    >r
    r@ open-input-file
    r> str-free
;

: src-read-source-line ( fileid -- str true | false = Read a line from the source )
    \ ." read-source line" cr
    str-new
    source-line-size 2 + over str-size!            \ Insure the size of the line
    tuck str-data@ source-line-size
    rot read-line throw IF
	over str-length!
	true
    ELSE
	drop
	str-free
	false
    THEN
;

: src-parse-source-line ( str -- docu true | false = Parse the source line )
    >r
    chr.sp r@ str-append-char
    r@ str-get tis2 tis-set
    BEGIN
	tis2 tis-skip-spaces drop
	chr.sp tis2 tis-scan-char
    WHILE
	    ele-name
    REPEAT
    s" end-line" ele-name
    r> str-free
;
  
\ ------------------------------------------------------------------------------
\ Convert the source files to documentation
\ ------------------------------------------------------------------------------
\ s" grid-03.fs" r/o open-file throw dup  ' tis-reader   tis2 tis-set-reader   \ Setup a reader with a file

0 value file.input
: open-input ( c-addr u -- )
    r/o open-file throw to file.input
;

\ s" grid-03.fs" open-input
\ s" fsdocgen.fs" open-input
\ s" grid-03.fs" r/o open-file throw value file.input
\ file.input ' tis-reader   tis2 tis-set-reader
: close-input ( -- )
    file.input close-file throw
;

: src-convert-to-documentation  (  -- = Convert a source file to html )
  \ start-reading-source
    BEGIN
\	." begin convert" cr
    file.input src-read-source-line
    WHILE
\	    ." while convert" cr
    src-parse-source-line 
\      over write-documentation
  REPEAT
\   stop-reading-source
;
\ Этот вариант сейчас работает как надо.
\ В следующей версии надо будет преобразовать его в xt
\ Кроме этого выяснилось, что теперь нет конца для
\ комментария backslash
\ Такой комментарий начинается символом backslash
\ конец твкого комментария это конец строки
\ Тогда надо, если начало комментария, то все остальное в этой строке
\ это закомментировано.
\ 09/01/19 Конец строки сделал. Работает как надо
\ Теперь можно приступать  к части построения компилятора
\ т.е. обработчика того, что получено на этапе лексического анализа
\ для этого создадим следующую версию файла
\ src-tree-01.00.fs --> src-tree-02.00.fs
\ вызов этого следующим предложением
\ src-convert-to-documentation

: src-parse ( c-addr u -- )
    .s ." src parse" type cr
;

: scw-execute      ( i*x xt snl -- j*x = Execute xt for every node in list )
  chr.sp  tis2 tis-scan-char                 \ walk = first
  BEGIN
    tis2 tis-eof?                   \ while walk<>nil do
  WHILE
    2>r 
    2r@ swap execute         \  execute xt with node
    2r>
    chr.sp  tis2 tis-scan-char                \  walk = walk->next
  REPEAT
  drop
;

: src-execute ( xt tis -- )
    ." src execute" 
    >r \ chr.sp r@ tis-scan-char
    BEGIN
	\ ." begin" \ .s cr
	r@ tis-skip-spaces drop
	chr.sp r@ tis-scan-char \ .s
	\ r@ tis-skip-spaces
	\ r@ tis-eof? 
    WHILE
	    \ .s ." while" 
	    rot dup >r execute r> \ .s cr
	    \ chr.sp r@ tis-scan-char IF drop THEN
	    \ drop
    REPEAT
    r>
    2drop
;

\ ' src-parse tis2 src-execute \ эта штука работает !!!!!!!!!!
\ но не так как надо. выбирает два раза подряд тис.


\ Scan with the reader 
: show-links   ( -- = example: Type all links in html file )
  ." Src tree" cr
  BEGIN
    false
      chr.sp  tis2 tis-scan-char IF        \ Это сканирует весь файл
	  \ теперь надо анализировать полученное
	  \ type cr \ Type leading string = link
	  ['] src-parse execute
    ELSE
	true ." end scan" cr
    THEN
  UNTIL
;
\ Scan with the reader 
: show-links-old-01   ( -- = example: Type all links in html file )
  ." Src tree" cr
  BEGIN
    false
    chr.sp  tis2 tis-scan-char IF        \ Это сканирует весь файл
	type cr \ Type leading string = link
    ELSE
	true ." end scan" cr
    THEN
  UNTIL
;

(
prt-var snl-first@ prt>defs-iter sni-first def>name str-get type lpoint-new ok
prt-var snl-first@ prt>defs-iter sni-first def>body str-get type
lpoint% allocate throw >r
r@ lpoint>snn snn-init
0 r@ lpoint>grdpoint ! r> ok
)

: src-def-body-type ( -- )
    prt-var snl-first@ prt>defs-iter sni-first >r
    BEGIN
	r@ nil <> IF
	    r@ def>name str-get type cr
	    r@ def>body str-get type cr
	    r> drop
	    true
	ELSE
	    false
	THEN
    WHILE
	    prt-var snl-first@ prt>defs-iter sni-next >r
    REPEAT
    r> drop

;

: src-def-name-type ( -- )
    prt-var snl-first@ prt>defs-iter sni-first >r
    BEGIN
	r@ nil <> IF
	    r@ def>name str-get type cr
	    r> drop
	    true
	ELSE
	    false
	THEN
    WHILE
	    prt-var snl-first@ prt>defs-iter sni-next >r
    REPEAT
    r> drop
;

: def-find-in-body ( str def -- )
.s ." def find in body" cr
    >r
    dup str-get 0 r@ def>body str-find .
    r> drop
;
\ Здесь происходит поиск так кат задумано.
\ Осталось добавить создание узла pnt% для defpnts
\ В этой точке перенесем все изменения в файл src-tree-02.00.fs
\ и сделаем комит.

: src-def-find-in-body ( -- )
    prt-var snl-first@ prt>defs-iter sni-first >r
    BEGIN
	r@ nil <> IF
	    r@ def>name  ['] def-find-in-body prt-var snl-first@ prt>defs snl-execute
	    drop
	    r> drop
	    true
	ELSE
	    false
	THEN
    WHILE
	    ." WHILE src-def-find-in-body" cr
	    prt-var snl-first@ prt>defs-iter sni-next >r
    REPEAT
    r> drop
;

: stack-free ( stack -- )
    >r
    BEGIN
	r@ snl-empty? 0= IF
	    \ ." stack is not empty" cr
	    true
	ELSE
	    \ ." stack is empty" cr
	    false
	ENDIF
    WHILE
	    r@ snl-pop free throw
	    \ r@ snl-dump
    REPEAT
    r> snl-free
;

: src-r1 ( str node -- )
    ( Ищет в node>body вхождение строки str
    возвращает количество вхождений
    Если 0 - ничего не найдено )

    (
tmp-str prt-var snl-first@ prt>defs snl-last@ def>body str^ccompare  ok
.s <1> 1  ok
tmp-str str-get 0 prt-var snl-first@ prt>defs snl-last@ def>body str-find  ok
.s <2> 1 39  ok


    )
    
;


: main ( -- )
    s" fsdocgen.fs" open-input
    \ s" grid-03.fs" open-input
    src-convert-to-documentation
    src-def-name-type
    src-def-body-type

;

: all-free ( -- )
    file.input close-file throw
    prt-var @ prt-free
    tis2 tis-free
    stack stack-free
;

\ show-links

\ Done, close the file

\ file.input close-file throw
\ prt-var @ prt-free

\ char : tis2 tis-scan-char [IF] type [THEN] 
\ tis2 str-get type cr

\ Free the stream from the heap

\ tis2 tis-free

