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
				if (Enum <= 38) then
					if (Enum <= 18) then
						if (Enum <= 8) then
							if (Enum <= 3) then
								if (Enum <= 1) then
									if (Enum == 0) then
										Stk[Inst[2]] = Stk[Inst[3]];
									elseif (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 2) then
									do
										return Stk[Inst[2]];
									end
								else
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 5) then
								if (Enum > 4) then
									do
										return Stk[Inst[2]];
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
										if (Mvm[1] == 68) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								end
							elseif (Enum <= 6) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							elseif (Enum > 7) then
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 13) then
							if (Enum <= 10) then
								if (Enum == 9) then
									local B = Inst[3];
									local K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 11) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 12) then
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 15) then
							if (Enum == 14) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 16) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 17) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 28) then
						if (Enum <= 23) then
							if (Enum <= 20) then
								if (Enum == 19) then
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
							elseif (Enum <= 21) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 22) then
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
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 25) then
							if (Enum > 24) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							end
						elseif (Enum <= 26) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum > 27) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 33) then
						if (Enum <= 30) then
							if (Enum == 29) then
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 31) then
							Stk[Inst[2]] = #Stk[Inst[3]];
						elseif (Enum == 32) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 35) then
						if (Enum > 34) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 36) then
						Stk[Inst[2]] = Inst[3];
					elseif (Enum > 37) then
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 58) then
					if (Enum <= 48) then
						if (Enum <= 43) then
							if (Enum <= 40) then
								if (Enum > 39) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 41) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							elseif (Enum > 42) then
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 45) then
							if (Enum > 44) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 46) then
							do
								return;
							end
						elseif (Enum > 47) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						end
					elseif (Enum <= 53) then
						if (Enum <= 50) then
							if (Enum > 49) then
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
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 51) then
							Stk[Inst[2]] = {};
						elseif (Enum == 52) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
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
					elseif (Enum <= 55) then
						if (Enum == 54) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							do
								return;
							end
						end
					elseif (Enum <= 56) then
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 57) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 68) then
					if (Enum <= 63) then
						if (Enum <= 60) then
							if (Enum == 59) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							else
								local A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
							end
						elseif (Enum <= 61) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum > 62) then
							Stk[Inst[2]] = {};
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
					elseif (Enum <= 65) then
						if (Enum > 64) then
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
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
								if (Mvm[1] == 68) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 66) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum == 67) then
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					else
						Stk[Inst[2]] = Stk[Inst[3]];
					end
				elseif (Enum <= 73) then
					if (Enum <= 70) then
						if (Enum > 69) then
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
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						end
					elseif (Enum <= 71) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 72) then
						local A = Inst[2];
						Stk[A] = Stk[A]();
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 75) then
					if (Enum > 74) then
						Stk[Inst[2]] = Inst[3];
					elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 76) then
					Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
				elseif (Enum == 77) then
					local A = Inst[2];
					Stk[A](Stk[A + 1]);
				else
					local A = Inst[2];
					Stk[A] = Stk[A]();
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!173Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q001E67B1AE233361B3B7133303053Q00705613C5DE03093Q00F10FCE6147D67FF31503073Q0026BD569C201885030D3Q00CF729372D5798075B25DB449F203043Q00269C37C703083Q006973666F6C646572030A3Q006D616B65666F6C64657203013Q002F03043Q005341564503043Q004C4F414400453Q00123A3Q00013Q00201A5Q000200123A000100013Q00201A00010001000300123A000200013Q00201A00020002000400123A000300053Q00060C0003000A000100010004273Q000A000100123A000300063Q00201A00040003000700123A000500083Q00201A00050005000900123A000600083Q00201A00060006000A00064000073Q000100062Q00443Q00064Q00448Q00443Q00044Q00443Q00014Q00443Q00024Q00443Q00053Q00123A0008000B3Q00202A00080008000C4Q000A00073Q00124B000B000D3Q00124B000C000E4Q003E000A000C4Q003B00083Q00024Q000900073Q00124B000A000F3Q00124B000B00104Q00200009000B00024Q000A00073Q00124B000B00113Q00124B000C00124Q0020000A000C00022Q003F000B5Q00123A000C00136Q000D00094Q0011000C0002000200060C000C002E000100010004273Q002E000100123A000C00146Q000D00094Q0021000C000200014Q000C00093Q00124B000D00156Q000E000A4Q0002000C000C000E000640000D0001000100022Q00443Q000C4Q00443Q00083Q000640000E0002000100022Q00443Q000C4Q00443Q00086Q000F000D4Q004E000F0001000200064000100003000100032Q00443Q000E4Q00443Q000F4Q00443Q00073Q001036000B0016001000064000100004000100022Q00443Q00074Q00443Q000F3Q001036000B001700102Q0003000B00024Q002E3Q00013Q00053Q00023Q00026Q00F03F026Q00704002264Q003F00025Q00124B000300014Q001F00045Q00124B000500013Q0004460003002100012Q001700078Q000800024Q0017000900014Q0017000A00024Q0017000B00034Q0017000C00046Q000D8Q000E00063Q00202B000F000600012Q003E000C000F4Q003B000B3Q00022Q0017000C00034Q0017000D00046Q000E00014Q001F000F00014Q0026000F0006000F00104C000F0001000F2Q001F001000014Q002600100006001000104C00100001001000202B0010001000012Q003E000D00104Q0010000C6Q003B000A3Q000200202F000A000A00022Q00130009000A4Q001500073Q00010004320003000500012Q0017000300056Q000400024Q003D000300044Q000F00036Q002E3Q00017Q00043Q0003063Q00697366696C65028Q0003083Q007265616466696C65030A3Q004A534F4E4465636F646500173Q00123A3Q00014Q001700016Q00113Q0002000200062C3Q001400013Q0004273Q0014000100124B3Q00024Q0045000100013Q0026013Q0007000100020004273Q0007000100123A000200034Q001700036Q00110002000200024Q000100024Q0017000200013Q00202A0002000200044Q000400014Q003D000200044Q000F00025Q0004273Q000700010004273Q001600012Q003F8Q00033Q00024Q002E3Q00017Q00023Q0003093Q00777269746566696C65030A3Q004A534F4E456E636F646501083Q00123A000100014Q001700026Q0017000300013Q00202A0003000300024Q00056Q003E000300054Q001500013Q00012Q002E3Q00017Q000C3Q00028Q00026Q00F03F03063Q00747970656F6603063Q00BB696E211D7303083Q0023C81D1C4873149A03063Q000AABC3D6832B03073Q005479DFB1BFED4C03063Q00B543C4A23F4203083Q00A1DB36A9C05A305003053Q00652Q726F7203493Q00604C1624454B0465404C10305D18400E4C5B40285C5114654B47402409511437404C0765484C04655F430C304C020D305A5640274C0201655A56122C4745402A5B020E30444005370703043Q0045292260022F3Q00124B000200013Q00260100020007000100020004273Q000700012Q001700036Q0017000400014Q00210003000200010004273Q002E000100260100020001000100010004273Q0001000100123A000300036Q00046Q00110003000200022Q0017000400023Q00124B000500043Q00124B000600054Q002000040006000200063800030024000100040004273Q0024000100123A000300036Q000400014Q00110003000200022Q0017000400023Q00124B000500063Q00124B000600074Q002000040006000200064A0003002A000100040004273Q002A000100123A000300036Q000400014Q00110003000200022Q0017000400023Q00124B000500083Q00124B000600094Q002000040006000200064A0003002A000100040004273Q002A000100123A0003000A4Q0017000400023Q00124B0005000B3Q00124B0006000C4Q003E000400064Q001500033Q00012Q0017000300014Q002500033Q000100124B000200023Q0004273Q000100012Q002E3Q00017Q00073Q00028Q0003063Q00747970656F6603063Q00AFD7C5030C2C03063Q004BDCA3B76A6203053Q00652Q726F7203243Q002BB49D36D50BBECB3ED712AF9F6D9929BF9277D417A99F77DB07FA8A77CA16A88239DE4C03053Q00B962DAEB5701173Q00124B000100013Q00260100010001000100010004273Q0001000100123A000200026Q00036Q00110002000200022Q001700035Q00124B000400033Q00124B000500044Q002000030005000200064A00020012000100030004273Q0012000100123A000200054Q001700035Q00124B000400063Q00124B000500074Q003E000300054Q001500023Q00012Q0017000200014Q0018000200024Q0003000200023Q0004273Q000100012Q002E3Q00017Q00", GetFEnv(), ...);
