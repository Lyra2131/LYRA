local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 32) then
					if (Enum <= 15) then
						if (Enum <= 7) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									else
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum > 2) then
									Stk[Inst[2]] = Inst[3];
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								end
							elseif (Enum <= 5) then
								if (Enum == 4) then
									Stk[Inst[2]] = Upvalues[Inst[3]];
								else
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum == 6) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							end
						elseif (Enum <= 11) then
							if (Enum <= 9) then
								if (Enum > 8) then
									local A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 10) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 13) then
							if (Enum == 12) then
								local A = Inst[2];
								local Index = Stk[A];
								local Step = Stk[A + 2];
								if (Step > 0) then
									if (Index > Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								elseif (Index < Stk[A + 1]) then
									VIP = Inst[3];
								else
									Stk[A + 3] = Index;
								end
							else
								local A = Inst[2];
								local Step = Stk[A + 2];
								local Index = Stk[A] + Step;
								Stk[A] = Index;
								if (Step > 0) then
									if (Index <= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Index >= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							end
						elseif (Enum > 14) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 34) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 23) then
						if (Enum <= 19) then
							if (Enum <= 17) then
								if (Enum == 16) then
									VIP = Inst[3];
								else
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum > 18) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							else
								local NewProto = Proto[Inst[3]];
								local NewUvals;
								local Indexes = {};
								NewUvals = Setmetatable({}, {__index=function(_, Key)
									local Val = Indexes[Key];
									return Val[1][Val[2]];
								end,__newindex=function(_, Key, Value)
									local Val = Indexes[Key];
									Val[1][Val[2]] = Value;
								end});
								for Idx = 1, Inst[4] do
									VIP = VIP + 1;
									local Mvm = Instr[VIP];
									if (Mvm[1] == 34) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 21) then
							if (Enum > 20) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum > 22) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]];
						end
					elseif (Enum <= 27) then
						if (Enum <= 25) then
							if (Enum > 24) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								VIP = Inst[3];
							end
						elseif (Enum == 26) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 29) then
						if (Enum == 28) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 30) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 31) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 48) then
					if (Enum <= 40) then
						if (Enum <= 36) then
							if (Enum <= 34) then
								if (Enum > 33) then
									Stk[Inst[2]] = Stk[Inst[3]];
								elseif (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 35) then
								do
									return;
								end
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 38) then
							if (Enum > 37) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 39) then
							local A = Inst[2];
							local Step = Stk[A + 2];
							local Index = Stk[A] + Step;
							Stk[A] = Index;
							if (Step > 0) then
								if (Index <= Stk[A + 1]) then
									VIP = Inst[3];
									Stk[A + 3] = Index;
								end
							elseif (Index >= Stk[A + 1]) then
								VIP = Inst[3];
								Stk[A + 3] = Index;
							end
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 44) then
						if (Enum <= 42) then
							if (Enum > 41) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = #Stk[Inst[3]];
							end
						elseif (Enum == 43) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 46) then
						if (Enum > 45) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum == 47) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 56) then
					if (Enum <= 52) then
						if (Enum <= 50) then
							if (Enum == 49) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							end
						elseif (Enum == 51) then
							Stk[Inst[2]] = Inst[3];
						else
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 54) then
						if (Enum > 53) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 55) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Stk[A + 1]));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						do
							return;
						end
					end
				elseif (Enum <= 60) then
					if (Enum <= 58) then
						if (Enum == 57) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum == 59) then
						Stk[Inst[2]] = {};
					else
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					end
				elseif (Enum <= 62) then
					if (Enum == 61) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 63) then
					Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
				elseif (Enum > 64) then
					do
						return Stk[Inst[2]];
					end
				else
					Stk[Inst[2]] = #Stk[Inst[3]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!393Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E736572742Q033Q004D31AE03073Q00B32654D72976DC03063Q00D5550F737CAD03053Q004E9E30764203053Q00EDAA28193203063Q00B69BCB4470562Q0103043Q00BAF952A003043Q00C5DE982603143Q00AE102AB6301764B1112CD12F176CA81122B6297C03073Q00569C2018851D2603023Q00AE9503073Q0037C7E523C81D1C030C3Q0023A992654227B489635D20AB03053Q0073149ABC542Q033Q002QDA9403063Q00DFB1BFED4CE103063Q007DCCB96E056603073Q00DB36A9C05A305003053Q005F430C2C4D03043Q0045292260010003043Q00B8C2C30F03063Q004BDCA3B76A6203143Q0050EAD9639453E8C6668936E8DB6D8A52E0DB67E303053Q00B962DAEB5703023Q00C22C03063Q00CAAB5C4786BE030B3Q0078987EC6789774C6788F7D03043Q00E849A14C2Q033Q00B0DC5B03053Q007EDBB9223D030D3Q003CDC5B7F7762FECC09D7092A2703083Q00876CAE3E121E179303053Q00A0E826C21C03083Q00A7D6894AAB78CE5303043Q008FF1265803063Q00C7EB90523D9803143Q005546EB7F4A47EB66574F8D7A524CE87E5D47EC1103043Q004B6776D903023Q00CE4403063Q007EA7341074D903083Q00997E6ED0FA49B29A03073Q009CA84E40E0D479030F3Q003EE1B0DC34EBA6DC02FA91C10CEBAB03043Q00AE678EC503083Q004745545F4B45595300873Q00122B3Q00013Q00203D5Q000200122B000100013Q00203D00010001000300122B000200013Q00203D00020002000400122B000300053Q00062F0003000A000100010004103Q000A000100122B000300063Q00203D00040003000700122B000500083Q00203D00050005000900122B000600083Q00203D00060006000A00061200073Q000100062Q00223Q00064Q00228Q00223Q00044Q00223Q00014Q00223Q00024Q00223Q00054Q002D00086Q002D000900034Q002D000A3Q00042Q0016000B00073Q001233000C000B3Q001233000D000C4Q0025000B000D00022Q0016000C00073Q001233000D000D3Q001233000E000E4Q0025000C000E00022Q001F000A000B000C2Q0016000B00073Q001233000C000F3Q001233000D00104Q0025000B000D000200202A000A000B00112Q0016000B00073Q001233000C00123Q001233000D00134Q0025000B000D00022Q0016000C00073Q001233000D00143Q001233000E00154Q0025000C000E00022Q001F000A000B000C2Q0016000B00073Q001233000C00163Q001233000D00174Q0025000B000D00022Q0016000C00073Q001233000D00183Q001233000E00194Q0025000C000E00022Q001F000A000B000C2Q002D000B3Q00042Q0016000C00073Q001233000D001A3Q001233000E001B4Q0025000C000E00022Q0016000D00073Q001233000E001C3Q001233000F001D4Q0025000D000F00022Q001F000B000C000D2Q0016000C00073Q001233000D001E3Q001233000E001F4Q0025000C000E000200202A000B000C00202Q0016000C00073Q001233000D00213Q001233000E00224Q0025000C000E00022Q0016000D00073Q001233000E00233Q001233000F00244Q0025000D000F00022Q001F000B000C000D2Q0016000C00073Q001233000D00253Q001233000E00264Q0025000C000E00022Q0016000D00073Q001233000E00273Q001233000F00284Q0025000D000F00022Q001F000B000C000D2Q002D000C3Q00042Q0016000D00073Q001233000E00293Q001233000F002A4Q0025000D000F00022Q0016000E00073Q001233000F002B3Q0012330010002C4Q0025000E001000022Q001F000C000D000E2Q0016000D00073Q001233000E002D3Q001233000F002E4Q0025000D000F000200202A000C000D00112Q0016000D00073Q001233000E002F3Q001233000F00304Q0025000D000F00022Q0016000E00073Q001233000F00313Q001233001000324Q0025000E001000022Q001F000C000D000E2Q0016000D00073Q001233000E00333Q001233000F00344Q0025000D000F00022Q0016000E00073Q001233000F00353Q001233001000364Q0025000E001000022Q001F000C000D000E2Q00070009000300012Q0016000A00073Q001233000B00373Q001233000C00384Q0025000A000C0002000612000B0001000100032Q00223Q000A4Q00223Q00074Q00223Q00093Q00102C00080039000B2Q0041000800024Q00373Q00013Q00023Q00023Q00026Q00F03F026Q00704002264Q002D00025Q001233000300014Q002900045Q001233000500013Q0004060003002100012Q003E00076Q0016000800024Q003E000900014Q003E000A00024Q003E000B00034Q003E000C00044Q0016000D6Q0016000E00063Q00202Q000F000600012Q001E000C000F4Q0020000B3Q00022Q003E000C00034Q003E000D00044Q0016000E00014Q0029000F00014Q0031000F0006000F00103C000F0001000F2Q0029001000014Q003100100006001000103C00100001001000202Q0010001000012Q001E000D00104Q0019000C6Q0020000A3Q0002002026000A000A00022Q00380009000A4Q000500073Q000100040D0003000500012Q003E000300054Q0016000400024Q0036000300044Q003900036Q00373Q00017Q00043Q00028Q0003053Q00652Q726F72031D3Q00772B5C3D364DB8522D5131205AA21601512E2452F152684B372E5BF61803073Q009836483F58453E01103Q001233000100013Q00260F00010001000100010004103Q000100012Q003E00025Q0006243Q000C000100020004103Q000C000100122B000200024Q003E000300013Q001233000400033Q001233000500044Q001E000300054Q000500023Q00012Q003E000200024Q0041000200023Q0004103Q000100012Q00373Q00017Q00", GetFEnv(), ...);
