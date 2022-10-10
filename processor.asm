
%macro compare 2						; compare(a, b) => TRUE/FALSE in rax
	and		rax, 0
	or		rax, %2						
	not		rax							; l = ~b
	and		rax, %1						; l = a & ~b
	and		rdi, 0
	or		rdi, %1
	not		rdi							; r = ~a
	and		rdi, %2						; r = ~a & b
	or		rax, rdi					; (a & ~b) | (~a & b)
	lahf
	shr		rax, 14						; ZF
	and		rax,  0x1
%endmacro

%macro get_reg_part 3					; get_reg_part(reg, start_bit, end_bit) => reg_part in rax
	compare 64, %3
	shl		rax, 63						; is64 = { 0xF..FF & (end_bit==64) } | { 0x0 & ~(end_bit==64) }
	sar		rax, 63
	and		rdi, 0
	or		rdi, 0xFFFFFFFFFFFFFFFF		; chunk_start = 0xF..F << start_bit
	shl		rdi, %2
	and		rsi, 0
	or		rsi, 0xFFFFFFFFFFFFFFFF		; chunk_end = ~(0xF..F << end_bit)
	shl		rsi, %3
	not		rsi
	or		rax, rsi					; chunk_end  = is_64 | chunk_end
	and		rax, rdi					; chunk = chunk_start & chunk_end
	and 	rax, %1						; reg_part = reg & chunk 
	shr		rax, %2						; reg_part = reg_part >> start_bit
%endmacro

%macro set_reg 4 						; set_reg(reg, start_bit, end_bit, data) => new reg output in rax
	compare 64, %3
	shl		rax, 63						; is64 = { 0xF..FF & (end_bit==64) } | { 0x0 & ~(end_bit==64) }
	sar		rax, 63
	and		rdi, 0
	or		rdi, 0xFFFFFFFFFFFFFFFF		; chunk_start = 0xF..F << start_bit
	shl		rdi, %2
	and		rsi, 0
	or		rsi, 0xFFFFFFFFFFFFFFFF		; chunk_end = ~(0xF..F << end_bit)
	shl		rsi, %3
	not		rsi
	or		rax, rsi					; chunk_end  = is_64 | chunk_end
	and		rax, rdi					; chunk = chunk_start & chunk_end
	and		rdi, 0
	or		rdi, %4						; data = data << start_bit
	shl		rdi, %2
	and 	rdi, rax					; data = data & chunk
	not		rax							; chunk = ~chunk
	and		rax, %1						; reg = reg & chunk
	or		rax, rdi					; reg = reg | data
%endmacro

%macro and_64 2							; and_64(boolean, data) =>  if (boolean) return data, if (~boolean) return 0. Output in rax.
	and		rax, 0
	or		rax, %1						; store boolean in rax
	shl 	rax, 63
	sar		rax, 63						; rax = 0xF..FF if bool is 1, or 0x0 if bool is 0
	and		rax, %2						; rax =  rax & data
%endmacro

%macro _p_ 1
	mov		[rel restore], rax
	mov		[rel restore+1*8], rbx
	mov		[rel restore+2*8], rcx
	mov		[rel restore+3*8], rdx
	mov 	[rel restore+4*8], rdi
	mov   	[rel restore+5*8], rsi
	movq	[rel restore+6*8], xmm0
	lea rdi, [rel format]
	and rsi, 0
	or	rsi, %1
	xor rax, rax
	call _printf
	mov		rax, [rel restore]
	mov		rbx, [rel restore+1*8]
	mov		rcx, [rel restore+2*8]
	mov		rdx, [rel restore+3*8]
	mov	 	rdi, [rel restore+4*8]
	mov	    rsi, [rel restore+5*8]
	movq 	xmm0, [rel restore+6*8]
%endmacro
section .data
 	format: db "%llu", 0xa, 0
	mem: dq 8388608 dup(5)
	restore: dq 8 dup(0)
section .text
	global _main
	extern _printf
_main:
	push rbp
	mov rbp, rsp
	; and rsp, 0xFFFFFFFFFFFFFFE0

	; lea rdi, [rel mem]
	and rdi, 0
	movq xmm0, rdi						; init RIP with 0

						mov	r8, 128
						mov r13, 1300
						mov r12, 3
						shl r12, 28
						or 	r12, 0x10000
						mov r11, 0xFFFFFFFFFFFFFFFF

						



;---------- xR11[0,32] ----------;

			; xR11[0,32] = 
		; 1 ; 			{ (xR8==69) (xR13[0,32]) } +
		; 2	; 			{ (xR8==194) ( (0 ≤ xR12[15,23] ≤ 2) (xR12[28,32]) + (xR12[15,23]==59) (xR12[32,40]) ) } +
		; 3	; 			{ (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } +
		; 4	; 			{ (xR8==128) (RCF[3,5]==0) (RIP)mem } +
		; 5	; 			{ ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32]) }

;-- 2 --;
	;========== (0 ≤ xR12[15,23] ≤ 2) (xR12[28,32]) ==========;

	and rcx, 0
	or	rcx, r12						
	shr rcx, 15							; rcx = icode (lower byte)
	and rdx, 0
	or	rdx,rcx							; rdx = icode (lower byte)
	and	rcx, 0x1						; rcx = 1st bit of icode
	and rdx, 0x2
	shr rdx, 1							; rdx = 2nd bit of icode
	compare	rcx, rdx					; rax = (1st bit == 2nd bit)
	not rax		
	and rdx, 0
	or	rdx, rax						; rdx = ~(1st bit == 2nd bit)
	and rcx, 0							
	or 	rcx, r12
	and rcx, 0x007F8000
	shr	rcx, 17							; rcx = icode omitting first 2 bits
	compare rcx, 0						; rax = (icode>>2 == 0)
	and rdx, rax						; rdx = ~(1st bit == 2nd bit) & (icode>>2 == 0)
	and rcx, 0
	or  rcx, r12
	and rcx, 0x007F8000
	shr rcx, 15
	compare rcx, 0						; rax = (icode==0)
	or rdx, rax							; rdx = {~(1st bit == 2nd bit) (icode>>2 == 0)} + {icode==0}
	and rcx, 0
	or rcx, r12
	shr rcx, 28
	and rcx, 0xF						; rcx = r12[28,32]
	and_64 rdx, rcx						
	and rdx, 0
	or	rdx, rax						; rdx = { ~(1st bit == 2nd bit) (icode>>2 == 0) + (icode==0) } { r12[28,32] }

	;********** (0 ≤ xR12[15,23] ≤ 2) (xR12[28,32]) **********;

	;========== (xR12[15,23]==59) (xR12[32,40]) ==========;

	and	rcx, 0
	or	rcx, r12
	and rcx, 0x007F8000
	shr rcx, 15							; rcx = icode
	compare rcx, 59
	and rcx, 0
	or 	rcx, rax						; rcx = (icode==59)
	and rdi, 0
	or 	rdi, r12
	shr rdi, 32							
	and rdi, 0x000000FF					; rdi = r12[32,40]
	and_64 rcx, rdi						; rax =  (icode==59) (r12[32,40])

	;********** (xR12[15,23]==59) (xR12[32,40]) **********;

	or	rdx, rax						; rdx = (0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])

	;========== { (xR8==194) ( (0 ≤ xR12[15,23] ≤ 2) (xR12[28,32]) + (xR12[15,23]==59) (xR12[32,40]) ) } ==========;

	compare r8, 194
	and rcx, 0
	or	rcx, rax						; rcx = (icode==194)
	and_64 rcx, rdx						; rax = {r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])}
	and rdx, 0
	or	rdx, rax						; rdx = {r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])}

	;********** { (xR8==194) ( (0 ≤ xR12[15,23] ≤ 2) (xR12[28,32]) + (xR12[15,23]==59) (xR12[32,40]) ) } **********;
;-- /2 --;


;-- 1 --;
	;========== { (xR8==69) (xR13[0,32]) } ==========;

	compare	r8, 69
	and	rcx, 0
	or	rcx, rax	
	and	r13d, r13d					
	and_64 rcx, r13 					; rax = (r8==69)(r13[0,32])
						
	;********** { (xR8==69) (xR13[0,32]) } **********;
;-- /1 --;

	or	rdx, rax						; rdx = {(r8==69)(r13[0,32])} +
										;		{r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])} 

;-- 3 --; 			
	;========== { (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } ==========;

	and rcx, 0
	or	rcx, r12
	and rcx, 0x007F8000
	shr rcx, 15							; rcx = icode
	compare rcx, 32						; rax = (xR12[15,23]==32)
	and	rcx, 0
	or	rcx, rax						; rcx = (xR12[15,23]==32)
	compare r8, 192						; rax = (xR8==192)
	and rcx, rax						; rcx = (xR8==192) (xR12[15,23]==32)
	and rdi, 0
	or  rdi, r13
	shr rdi, 32							
	and	edi, edi 						; rdi = xR13[32,64]
	and_64 rcx, rdi 					; rax = (xR8==192) (xR12[15,23]==32) (xR13[32,64])			

	;********** { (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } **********;

	or  rdx, rax						; rdx = {(r8==69)(r13[0,32])} +
										;		{r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])} +
										;		{ (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } +

	
;-- 4 --; 			
	;========== { (xR8==128) (RCF[3,5]==0) (RIP)mem } ==========;

	movq  rcx, xmm3					
	shr	  rcx, 3	
	and	  rcx, 0x00000003				; rcx = RCF[3,5] (PROGRAM_STATUS_REGISTER)
	compare rcx, 0						; rax = (RCF[3,5]==0)
	and   rcx, 0
	or	  rcx, rax						; rcx = (RCF[3,5]==0)
	compare r8, 128						; rax = (xR8==128)
	and	  rcx, rax						; rcx = (xR8==128) (RCF[3,5]==0)
	movq  rax, xmm0
	;and   eax, eax 					; rax = RIP
	lea	  rsi, [rel mem]				; rsi = base
	and   rdi, 0
	or    rdi, [rsi+rax]				; rdi = (RIP)mem
	and_64 rcx, rdi						; rax = (xR8==128) (RCF[3,5]==0) (RIP)mem

	;********** { (xR8==128) (RCF[3,5]==0) (RIP)mem } **********;

	or rdx, rax							; rdx = {(r8==69)(r13[0,32])} +
										;		{r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])} +
										;		{ (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } +
										;		{ (xR8==128) (RCF[3,5]==0) (RIP)mem }  +

;-- 5 --; 			
	;========== { ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32]) } ==========;
	
	compare r8, 69						; rax = (xR8==69)
	and rsi, 0
	or	rsi, rax						
	not rsi								; rsi = ~(xR8==69)
	compare r8, 128				
	not rax
	and rsi, rax						; rsi = ~(xR8==69) ~(xR8==128)
	compare r8, 192
	not rax
	and rsi, rax						; rsi = ~(xR8==69) ~(xR8==128) ~(xR8==192)
	compare r8, 194
	not rax
	and rsi, rax						; rsi = ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194)
	and_64 rsi, r11						; rax = ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11)
	and eax, eax						; rax = ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32])

	;********** { ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32]) } **********;

	or rdx, rax							; rdx = {(r8==69)(r13[0,32])} +
										;		{r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])} +
										;		{ (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } +
										;		{ (xR8==128) (RCF[3,5]==0) (RIP)mem }  +
										;		{  ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32]) }

	and edx, edx						; ensure high bits are zeroed out		
	and rax, 0
	or	rax, 0xFFFFFFFFFFFFFFFF
	shl	rax, 32
	and	r11, rax						; xR11[0,32] = 0x0..00
	or	r11, rdx						; xR11[0,32] = {(r8==69)(r13[0,32])} +
										;		{r8==194} {(0≤icode≤2) (r12[28,32]) + (icode==59) (r12[32,40])} +
										;		{ (xR8==192) (xR12[15,23]==32) (xR13[32,64]) } +
										;		{ (xR8==128) (RCF[3,5]==0) (RIP)mem }  +
										;		{  ~(xR8==69) ~(xR8==128) ~(xR8==192) ~(xR8==194) (xR11[0,32]) }

;********** xR11[0,32] **********;



	_p_ r11
	; xor rsi, rsi
	; lea rax, [rel mem]
	; mov r9, 10
	; movq xmm0, r9
	; movq r9, xmm1
	; add rax, 0
	; or byte [rel mem], 100
	; or  sil, [rel rax]
	; mov rax, 0
	
	

	mov rsp, rbp
	pop rbp
	ret

