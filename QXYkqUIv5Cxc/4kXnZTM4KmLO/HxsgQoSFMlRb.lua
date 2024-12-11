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
				if (Enum <= 42) then
					if (Enum <= 20) then
						if (Enum <= 9) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										local A = Inst[2];
										Stk[A] = Stk[A]();
									else
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum <= 2) then
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
								elseif (Enum > 3) then
									do
										return;
									end
								elseif not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 6) then
								if (Enum > 5) then
									if Stk[Inst[2]] then
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
							elseif (Enum <= 7) then
								Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							elseif (Enum > 8) then
								VIP = Inst[3];
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									Upvalues[Inst[3]] = Stk[Inst[2]];
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 12) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							elseif (Enum > 13) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 17) then
							if (Enum <= 15) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif (Enum == 16) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							end
						elseif (Enum <= 18) then
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 19) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 31) then
						if (Enum <= 25) then
							if (Enum <= 22) then
								if (Enum > 21) then
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Top));
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 23) then
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
									if (Mvm[1] == 11) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							elseif (Enum > 24) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							end
						elseif (Enum <= 28) then
							if (Enum <= 26) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 27) then
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							elseif (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 29) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						elseif (Enum > 30) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Top));
							end
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 36) then
						if (Enum <= 33) then
							if (Enum > 32) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							else
								do
									return;
								end
							end
						elseif (Enum <= 34) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						elseif (Enum == 35) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 39) then
						if (Enum <= 37) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						elseif (Enum > 38) then
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
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 40) then
						if (Stk[Inst[2]] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 41) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 64) then
					if (Enum <= 53) then
						if (Enum <= 47) then
							if (Enum <= 44) then
								if (Enum == 43) then
									Stk[Inst[2]] = Stk[Inst[3]];
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 45) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Enum > 46) then
								Stk[Inst[2]] = {};
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 50) then
							if (Enum <= 48) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							elseif (Enum == 49) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 51) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 52) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 58) then
						if (Enum <= 55) then
							if (Enum == 54) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 56) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum == 57) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 61) then
						if (Enum <= 59) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						elseif (Enum > 60) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local C = Inst[4];
							local CB = A + 2;
							local Result = {Stk[A](Stk[A + 1], Stk[CB])};
							for Idx = 1, C do
								Stk[CB + Idx] = Result[Idx];
							end
							local R = Result[1];
							if R then
								Stk[CB] = R;
								VIP = Inst[3];
							else
								VIP = VIP + 1;
							end
						end
					elseif (Enum <= 62) then
						Stk[Inst[2]] = #Stk[Inst[3]];
					elseif (Enum == 63) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Upvalues[Inst[3]];
					end
				elseif (Enum <= 75) then
					if (Enum <= 69) then
						if (Enum <= 66) then
							if (Enum == 65) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 67) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 68) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 72) then
						if (Enum <= 70) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 71) then
							do
								return Stk[Inst[2]];
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 73) then
						local A = Inst[2];
						local Results = {Stk[A](Stk[A + 1])};
						local Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum == 74) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					end
				elseif (Enum <= 80) then
					if (Enum <= 77) then
						if (Enum > 76) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 78) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif (Enum > 79) then
						for Idx = Inst[2], Inst[3] do
							Stk[Idx] = nil;
						end
					else
						Upvalues[Inst[3]] = Stk[Inst[2]];
					end
				elseif (Enum <= 83) then
					if (Enum <= 81) then
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
					elseif (Enum > 82) then
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
							if (Mvm[1] == 11) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
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
					end
				elseif (Enum <= 84) then
					local A = Inst[2];
					local C = Inst[4];
					local CB = A + 2;
					local Result = {Stk[A](Stk[A + 1], Stk[CB])};
					for Idx = 1, C do
						Stk[CB + Idx] = Result[Idx];
					end
					local R = Result[1];
					if R then
						Stk[CB] = R;
						VIP = Inst[3];
					else
						VIP = VIP + 1;
					end
				elseif (Enum > 85) then
					if (Inst[2] == Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Inst[2] == Stk[Inst[4]]) then
					VIP = VIP + 1;
				else
					VIP = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!1B3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B4Q0007606C1B16666A21107103043Q001C48731403353Q003C0DABC1CCD7937B0DB6DCDA8CCC3D57B6DE908CCC3D568BD8D28893370CADC3DA83C87B03B0DFDAD2C83D14BAEBD083D9692C8BF203073Q00BC5479DFB1BFED03223Q00C9AF42D9929BF419C891C8F55FD988C7A218C693C6F409CF8ED3B657DDDCCBA859C703053Q00E1A1DB36A9030F3Q00693F40377A47394235411146493F5E03073Q005A305035452922030A3Q006C6F6164737472696E6703073Q00482Q7470476574036A3Q0023A8D7C7E071F38CC5F23CF2C4DEE723A9C1C2E02EAEC0D8FD3FB9CDC3BD28B3CE98DF32AEC285A278ED8CFBCA199D8CC5F62DAF8CDFF62AB8D098FE2AB5CD98C21385C82QC602AA96F4EB28F3F2DDA71F92F4CDA73C8EF9DBBC25B7D5DDFD04ABC1F8DB3BB78DDBE62A03053Q00934BDCA3B703043Q004155544803083Q00434845432Q4B4559030A3Q00524556414C4944415445004E3Q002Q123Q00013Q0020155Q0002002Q12000100013Q002015000100010003002Q12000200013Q002015000200020004002Q12000300053Q0006340003000A0001000100040D3Q000A0001002Q12000300063Q002015000400030007002Q12000500083Q002015000500050009002Q12000600083Q00201500060006000A00061700073Q000100062Q000B3Q00064Q000B8Q000B3Q00044Q000B3Q00014Q000B3Q00024Q000B3Q00053Q002Q120008000B3Q00204400080008000C2Q002B000A00073Q001213000B000D3Q001213000C000E4Q0010000A000C4Q002300083Q00022Q004C00096Q002B000A00073Q001213000B000F3Q001213000C00104Q002E000A000C00022Q002B000B00073Q001213000C00113Q001213000D00124Q002E000B000D00022Q002B000C00073Q001213000D00133Q001213000E00144Q002E000C000E00022Q003A000D000D3Q002Q12000E00153Q002Q12000F000B3Q002044000F000F00162Q002B001100073Q001213001200173Q001213001300184Q0010001100134Q002A000F6Q0023000E3Q00022Q002D000E00010002000617000F0001000100032Q000B3Q00074Q000B3Q000C4Q000B3Q000D3Q00103B00090019000F000617000F0002000100032Q000B3Q00084Q000B3Q000A4Q000B3Q00073Q00061700100003000100032Q000B3Q00084Q000B3Q000B4Q000B3Q00073Q00061700110004000100052Q000B3Q00074Q000B3Q00104Q000B3Q000F4Q000B3Q000D4Q000B3Q000E3Q00103B0009001A001100061700110005000100012Q000B3Q00093Q00103B0009001B00112Q002C000900024Q00043Q00013Q00063Q00023Q00026Q00F03F026Q00704002264Q004C00025Q001213000300014Q003E00045Q001213000500013Q0004520003002100012Q000100076Q002B000800024Q0001000900014Q0001000A00024Q0001000B00034Q0001000C00044Q002B000D6Q002B000E00063Q00200C000F000600012Q0010000C000F4Q0023000B3Q00022Q0001000C00034Q0001000D00044Q002B000E00014Q003E000F00014Q0026000F0006000F001024000F0001000F2Q003E001000014Q002600100006001000102400100001001000200C0010001000012Q0010000D00104Q002A000C6Q0023000A3Q000200200E000A000A00022Q003D0009000A4Q004600073Q00010004510003000500012Q0001000300054Q002B000400024Q0018000300044Q001400036Q00043Q00017Q000D3Q00028Q0003063Q00747970656F6603063Q0039CD10B3850503063Q00624AB962DAEB03053Q00652Q726F72032D3Q0083C52A2615A3CF7C3316A1CE32671FA5D931260DE48B082812AFC57C2A0CB9DF7C251CEACA7C340DB8C232205703053Q0079CAAB5C4703053Q007072696E74031A3Q00739D3DC929D046812AC038D75D8669D239DD518D3AD22ACB5EC603063Q00BE32E849A14C03043Q007761726E031D3Q009ADA41580DA899465810B2DC46075E92D7545C12B2DD024911B0DC4C1303053Q007EDBB9223D01323Q001213000100013Q00264D000100010001000100040D3Q00010001002Q12000200024Q002B00036Q004E0002000200022Q000100035Q001213000400033Q001213000500044Q002E00030005000200061A000200120001000300040D3Q00120001002Q12000200054Q000100035Q001213000400063Q001213000500074Q0010000300054Q004600023Q00012Q0001000200013Q0006453Q00220001000200040D3Q00220001001213000200013Q00264D000200160001000100040D3Q001600012Q000A3Q00023Q002Q12000300084Q000100045Q001213000500093Q0012130006000A4Q0010000400064Q004600033Q000100040D3Q0031000100040D3Q0016000100040D3Q00310001001213000200013Q00264D000200230001000100040D3Q00230001002Q120003000B4Q000100045Q0012130005000C3Q0012130006000D4Q0010000400064Q004600033Q00012Q003A000300034Q000A000300023Q00040D3Q0031000100040D3Q0023000100040D3Q0031000100040D3Q000100012Q00043Q00017Q00053Q00028Q0003053Q007063612Q6C03053Q00652Q726F72032C3Q002ACF577E7B73B3F3038E58776A74FBA708CF4A773E76FDE34CDA577F7B372QF503C31E46777AF6A72DFE773C03083Q00876CAE3E121E1793001A3Q0012133Q00014Q003A000100023Q000E560001000200013Q00040D3Q00020001002Q12000300023Q00061700043Q000100022Q00408Q00403Q00014Q00490003000200042Q002B000200044Q002B000100033Q002Q060001001100013Q00040D3Q00110001002Q060002001100013Q00040D3Q001100012Q002C000200023Q00040D3Q00190001002Q12000300034Q0001000400023Q001213000500043Q001213000600054Q0010000400064Q004600033Q000100040D3Q0019000100040D3Q000200012Q00043Q00013Q00013Q00033Q00030A3Q004A534F4E4465636F646503043Q0067616D6503073Q00482Q747047657400094Q00017Q0020445Q0001002Q12000200023Q0020440002000200032Q0001000400014Q0010000200044Q001F8Q00148Q00043Q00017Q00063Q00028Q0003053Q007063612Q6C03023Q00697003053Q00652Q726F7203273Q0090E823C71DAA73D3B9A92CCE0CAD3B879FD96ACA1CAA21C2A5FA6ACD0AA13E879FD96AEA28877D03083Q00A7D6894AAB78CE53001B3Q0012133Q00014Q003A000100023Q000E560001000200013Q00040D3Q00020001002Q12000300023Q00061700043Q000100022Q00408Q00403Q00014Q00490003000200042Q002B000200044Q002B000100033Q002Q060001001200013Q00040D3Q00120001002Q060002001200013Q00040D3Q001200010020150003000200032Q002C000300023Q00040D3Q001A0001002Q12000300044Q0001000400023Q001213000500053Q001213000600064Q0010000400064Q004600033Q000100040D3Q001A000100040D3Q000200012Q00043Q00013Q00013Q00033Q00030A3Q004A534F4E4465636F646503043Q0067616D6503073Q00482Q747047657400094Q00017Q0020445Q0001002Q12000200023Q0020440002000200032Q0001000400014Q0010000200044Q001F8Q00148Q00043Q00017Q00273Q00028Q00027Q004003063Q006970616972732Q033Q006B6579026Q00F03F03053Q009DF13E54FC03063Q00C7EB90523D9803053Q0076616C696403043Q000317AD2E03043Q004B6776D903043Q006461746503023Q00CE4403063Q007EA7341074D903023Q0069702Q033Q00C32B3903073Q009CA84E40E0D47903053Q0011EFA9C72Q03043Q00AE678EC5010003073Q005B2D4C2B2459FD03073Q009836483F58453E031E3Q004B65792069736E277420706169726564207769746820746869732049502E03053Q00C2C5E255D003043Q003CB4A48E03073Q00555B163A26EA1703073Q0072383E6549478D03103Q0093ECC284B0E8C884BDF1CBCDAAECDF8A03043Q00A4D889BB03053Q00C4E73DBBA203073Q006BB28651D2C69E03073Q00350B91D5AB3F0B03053Q00CA586EE2A6030E3Q00E80A9BB7C4CC1BC2F1C5D60186B903053Q00AAA36FE29703083Q006461746554696D6503053Q00652Q726F72034F3Q003025A6304B393D1833B32C4738275122B7295B3E3B1434FC787E3B2C1023B7785C2227511CAB2A4F13280531FC197B03015924BD334B39605132B73E41252C5125A1314030693218971B651C0C287E03073Q00497150D2582E5703083Q004745545F4B455953017C3Q001213000100014Q003A000200043Q000E56000200600001000100040D3Q00600001002Q12000500034Q002B000600024Q004900050002000700040D3Q004E0001002015000A00090004000645000A004E00013Q00040D3Q004E0001001213000A00013Q00264D000A00280001000500040D3Q002800012Q004C000B3Q00042Q0001000C5Q001213000D00063Q001213000E00074Q002E000C000E0002002015000D000900082Q004A000B000C000D2Q0001000C5Q001213000D00093Q001213000E000A4Q002E000C000E0002002015000D0009000B2Q004A000B000C000D2Q0001000C5Q001213000D000C3Q001213000E000D4Q002E000C000E0002002015000D0009000E2Q004A000B000C000D2Q0001000C5Q001213000D000F3Q001213000E00104Q002E000C000E0002002015000D000900042Q004A000B000C000D2Q002C000B00023Q00264D000A000C0001000100040D3Q000C0001002015000B0009000E00061A000B00390001000300040D3Q003900012Q004C000B3Q00022Q0001000C5Q001213000D00113Q001213000E00124Q002E000C000E0002002030000B000C00132Q0001000C5Q001213000D00143Q001213000E00154Q002E000C000E0002002030000B000C00162Q002C000B00023Q002015000B0009000B000628000B004C0001000400040D3Q004C00012Q004C000B3Q00022Q0001000C5Q001213000D00173Q001213000E00184Q002E000C000E0002002030000B000C00132Q0001000C5Q001213000D00193Q001213000E001A4Q002E000C000E00022Q0001000D5Q001213000E001B3Q001213000F001C4Q002E000D000F00022Q004A000B000C000D2Q002C000B00023Q001213000A00053Q00040D3Q000C0001000654000500080001000200040D3Q000800012Q004C00053Q00022Q000100065Q0012130007001D3Q0012130008001E4Q002E0006000800020020300005000600132Q000100065Q0012130007001F3Q001213000800204Q002E0006000800022Q000100075Q001213000800213Q001213000900224Q002E0007000900022Q004A0005000600072Q002C000500023Q00264D000100690001000500040D3Q006900012Q0001000500014Q002D0005000100022Q002B000300054Q0001000500024Q002D000500010002002015000400050023001213000100023Q00264D000100020001000100040D3Q000200012Q0001000500033Q000634000500740001000100040D3Q00740001002Q12000500244Q000100065Q001213000700253Q001213000800264Q0010000600084Q004600053Q00012Q0001000500043Q0020150005000500272Q0001000600034Q004E0005000200022Q002B000200053Q001213000100053Q00040D3Q000200012Q00043Q00017Q00013Q0003083Q00434845432Q4B455901064Q000100015Q0020150001000100012Q002B00026Q0018000100024Q001400016Q00043Q00017Q00", GetFEnv(), ...);
