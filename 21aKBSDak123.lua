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
				if (Enum <= 39) then
					if (Enum <= 19) then
						if (Enum <= 9) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum > 0) then
										Stk[Inst[2]] = Inst[3];
									else
										local A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 2) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum > 3) then
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
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 6) then
								if (Enum == 5) then
									do
										return Stk[Inst[2]];
									end
								elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 7) then
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
							elseif (Enum == 8) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum <= 12) then
								Stk[Inst[2]] = {};
							elseif (Enum == 13) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 16) then
							if (Enum == 15) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 17) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						elseif (Enum == 18) then
							do
								return;
							end
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 29) then
						if (Enum <= 24) then
							if (Enum <= 21) then
								if (Enum > 20) then
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum <= 22) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum == 23) then
								local A = Inst[2];
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 26) then
							if (Enum > 25) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 27) then
							Stk[Inst[2]] = {};
						elseif (Enum > 28) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 34) then
						if (Enum <= 31) then
							if (Enum > 30) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 32) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 33) then
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
								if (Mvm[1] == 47) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 36) then
						if (Enum == 35) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						else
							local A = Inst[2];
							Stk[A] = Stk[A]();
						end
					elseif (Enum <= 37) then
						local A = Inst[2];
						local B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
					elseif (Enum > 38) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					else
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					end
				elseif (Enum <= 59) then
					if (Enum <= 49) then
						if (Enum <= 44) then
							if (Enum <= 41) then
								if (Enum == 40) then
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
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								end
							elseif (Enum <= 42) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 43) then
								if not Stk[Inst[2]] then
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
									if (Mvm[1] == 47) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 46) then
							if (Enum == 45) then
								Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 47) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif (Enum == 48) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
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
					elseif (Enum <= 54) then
						if (Enum <= 51) then
							if (Enum > 50) then
								do
									return;
								end
							else
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 52) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 53) then
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						end
					elseif (Enum <= 56) then
						if (Enum > 55) then
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
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 57) then
						VIP = Inst[3];
					elseif (Enum == 58) then
						Stk[Inst[2]] = Env[Inst[3]];
					else
						Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
					end
				elseif (Enum <= 69) then
					if (Enum <= 64) then
						if (Enum <= 61) then
							if (Enum > 60) then
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
						elseif (Enum <= 62) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
						elseif (Enum > 63) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 66) then
						if (Enum > 65) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum <= 67) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					elseif (Enum > 68) then
						Stk[Inst[2]] = Inst[3];
					else
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 74) then
					if (Enum <= 71) then
						if (Enum > 70) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum <= 72) then
						Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
					elseif (Enum == 73) then
						local A = Inst[2];
						do
							return Unpack(Stk, A, A + Inst[3]);
						end
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 77) then
					if (Enum <= 75) then
						local B = Inst[3];
						local K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
					elseif (Enum > 76) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					elseif (Stk[Inst[2]] == Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 78) then
					for Idx = Inst[2], Inst[3] do
						Stk[Idx] = nil;
					end
				elseif (Enum > 79) then
					Stk[Inst[2]] = Upvalues[Inst[3]];
				else
					local A = Inst[2];
					local B = Stk[Inst[3]];
					Stk[A + 1] = B;
					Stk[A] = B[Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!183Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q001EE854CD05F952CB3FFF4503043Q00BD569C2003093Q00517FCEC44275C5CB5E03043Q00851D269C030D3Q00B6669C93AC6D8F94CB49BBA88B03043Q00C7E523C803083Q006973666F6C646572030A3Q006D616B65666F6C64657203013Q002F03043Q005341564503043Q004C4F414403063Q0052454D4F5645004A3Q00123A3Q00013Q0020465Q000200123A000100013Q00204600010001000300123A000200013Q00204600020002000400123A000300053Q00062C0003000A000100010004393Q000A000100123A000300063Q00204600040003000700123A000500083Q00204600050005000900123A000600083Q00204600060006000A00062B00073Q000100062Q002F3Q00064Q002F8Q002F3Q00044Q002F3Q00014Q002F3Q00024Q002F3Q00053Q00123A0008000B3Q00202500080008000C2Q0014000A00073Q001245000B000D3Q001245000C000E4Q0017000A000C4Q004100083Q00022Q0014000900073Q001245000A000F3Q001245000B00104Q00160009000B00022Q0014000A00073Q001245000B00113Q001245000C00124Q0016000A000C00022Q001B000B5Q00123A000C00134Q0014000D00094Q0044000C0002000200062C000C002E000100010004393Q002E000100123A000C00144Q0014000D00094Q004D000C000200012Q0014000C00093Q001245000D00154Q0014000E000A4Q000A000C000C000E00062B000D0001000100022Q002F3Q000C4Q002F3Q00083Q00062B000E0002000100022Q002F3Q000C4Q002F3Q00084Q0014000F000D4Q0024000F0001000200062B00100003000100032Q002F3Q000E4Q002F3Q000F4Q002F3Q00073Q001026000B0016001000062B00100004000100022Q002F3Q00074Q002F3Q000F3Q001026000B0017001000062B00100005000100032Q002F3Q00074Q002F3Q000F4Q002F3Q000E3Q001026000B001800102Q0032000B00024Q00123Q00013Q00063Q00023Q00026Q00F03F026Q00704002264Q001B00025Q001245000300014Q000300045Q001245000500013Q0004280003002100012Q001100076Q0014000800024Q0011000900014Q0011000A00024Q0011000B00034Q0011000C00044Q0014000D6Q0014000E00063Q00203E000F000600012Q0017000C000F4Q0041000B3Q00022Q0011000C00034Q0011000D00044Q0014000E00014Q0003000F00014Q0027000F0006000F001013000F0001000F2Q0003001000014Q002700100006001000101300100001001000203E0010001000012Q0017000D00104Q0043000C6Q0041000A3Q0002002047000A000A00022Q00380009000A4Q004A00073Q00010004070003000500012Q0011000300054Q0014000400024Q0023000300044Q001A00036Q00123Q00017Q00043Q0003063Q00697366696C65028Q0003083Q007265616466696C65030A3Q004A534F4E4465636F646500173Q00123A3Q00014Q001100016Q00443Q000200020006303Q001400013Q0004393Q001400010012453Q00024Q004E000100013Q00264C3Q0007000100020004393Q0007000100123A000200034Q001100036Q00440002000200022Q0014000100024Q0011000200013Q0020250002000200042Q0014000400014Q0023000200044Q001A00025Q0004393Q000700010004393Q001600012Q001B8Q00323Q00024Q00123Q00017Q00023Q0003093Q00777269746566696C65030A3Q004A534F4E456E636F646501083Q00123A000100014Q001100026Q0011000300013Q0020250003000300022Q001400056Q0017000300054Q004A00013Q00012Q00123Q00017Q000C3Q00028Q00026Q00F03F03063Q00747970656F6603063Q003B076675261403043Q001C48731403063Q00270DADD8D18A03073Q00BC5479DFB1BFED03063Q00CFAE5BCB84D303053Q00E1A1DB36A903053Q00652Q726F7203493Q00793E4324454B3E10395B355C5660101B503C094F2F432415274C023B10234137404C3D10315B2109543B5C2550654457294470572009437A4324472C47457A5F22152B5C4F3855221B03073Q005A305035452922022F3Q001245000200013Q00264C00020007000100020004393Q000700012Q001100036Q0011000400014Q004D0003000200010004393Q002E000100264C00020001000100010004393Q0001000100123A000300034Q001400046Q00440003000200022Q0011000400023Q001245000500043Q001245000600054Q001600040006000200061000030024000100040004393Q0024000100123A000300034Q0014000400014Q00440003000200022Q0011000400023Q001245000500063Q001245000600074Q001600040006000200062A0003002A000100040004393Q002A000100123A000300034Q0014000400014Q00440003000200022Q0011000400023Q001245000500083Q001245000600094Q001600040006000200062A0003002A000100040004393Q002A000100123A0003000A4Q0011000400023Q0012450005000B3Q0012450006000C4Q0017000400064Q004A00033Q00012Q0011000300014Q001800033Q0001001245000200023Q0004393Q000100012Q00123Q00017Q00073Q00028Q0003063Q00747970656F6603063Q0038A8D1DEFD2C03053Q00934BDCA3B703053Q00652Q726F7203243Q0003D714BB870B2E990BB49B173E8342918E1B6AD417A99F4228DC42BBCB113ECB0BB48C4C03063Q00624AB962DAEB01173Q001245000100013Q00264C00010001000100010004393Q0001000100123A000200024Q001400036Q00440002000200022Q001100035Q001245000400033Q001245000500044Q001600030005000200062A00020012000100030004393Q0012000100123A000200054Q001100035Q001245000400063Q001245000500074Q0017000300054Q004A00023Q00012Q0011000200014Q001F000200024Q0032000200023Q0004393Q000100012Q00123Q00017Q00093Q00028Q0003063Q00747970656F6603063Q00B9DF2Q2E17AD03053Q0079CAAB5C4703053Q00652Q726F7203243Q007B863FC020D756C820CF3CCB46D269EA29C712853CD2389E508D69C06CCD469A20CF2B9003063Q00BE32E849A14C00026Q00F03F011D3Q001245000100013Q00264C00010015000100010004393Q0015000100123A000200024Q001400036Q00440002000200022Q001100035Q001245000400033Q001245000500044Q001600030005000200062A00020012000100030004393Q0012000100123A000200054Q001100035Q001245000400063Q001245000500074Q0017000300054Q004A00023Q00012Q0011000200013Q00202D00023Q0008001245000100093Q00264C00010001000100090004393Q000100012Q0011000200024Q0011000300014Q004D0002000200010004393Q001C00010004393Q000100012Q00123Q00017Q00", GetFEnv(), ...);
