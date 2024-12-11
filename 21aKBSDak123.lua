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
								elseif (Enum <= 2) then
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
								elseif (Enum > 3) then
									for Idx = Inst[2], Inst[3] do
										Stk[Idx] = nil;
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 6) then
								if (Enum == 5) then
									do
										return Stk[Inst[2]];
									end
								else
									local A = Inst[2];
									Stk[A] = Stk[A]();
								end
							elseif (Enum <= 7) then
								Stk[Inst[2]] = Stk[Inst[3]];
							elseif (Enum == 8) then
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 14) then
							if (Enum <= 11) then
								if (Enum == 10) then
									Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 12) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							elseif (Enum == 13) then
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
								local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								local Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 16) then
							if (Enum > 15) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 17) then
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						elseif (Enum > 18) then
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 29) then
						if (Enum <= 24) then
							if (Enum <= 21) then
								if (Enum == 20) then
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
										if (Mvm[1] == 7) then
											Indexes[Idx - 1] = {Stk,Mvm[3]};
										else
											Indexes[Idx - 1] = {Upvalues,Mvm[3]};
										end
										Lupvals[#Lupvals + 1] = Indexes;
									end
									Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
								else
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								end
							elseif (Enum <= 22) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							elseif (Enum == 23) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							else
								Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
							end
						elseif (Enum <= 26) then
							if (Enum == 25) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Upvalues[Inst[3]];
							end
						elseif (Enum <= 27) then
							if (Stk[Inst[2]] == Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 28) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						end
					elseif (Enum <= 34) then
						if (Enum <= 31) then
							if (Enum == 30) then
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A = Inst[2];
								local B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum <= 32) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						elseif (Enum > 33) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 36) then
						if (Enum == 35) then
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 37) then
						local A = Inst[2];
						do
							return Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum > 38) then
						Stk[Inst[2]] = {};
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					end
				elseif (Enum <= 59) then
					if (Enum <= 49) then
						if (Enum <= 44) then
							if (Enum <= 41) then
								if (Enum == 40) then
									if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 42) then
								for Idx = Inst[2], Inst[3] do
									Stk[Idx] = nil;
								end
							elseif (Enum == 43) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 46) then
							if (Enum > 45) then
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
									if (Mvm[1] == 7) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 47) then
							Stk[Inst[2]] = {};
						elseif (Enum == 48) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum <= 54) then
						if (Enum <= 51) then
							if (Enum > 50) then
								Stk[Inst[2]] = Env[Inst[3]];
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 52) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 53) then
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
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 56) then
						if (Enum == 55) then
							do
								return;
							end
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, A + Inst[3]);
							end
						end
					elseif (Enum <= 57) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					elseif (Enum == 58) then
						Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
					else
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum <= 69) then
					if (Enum <= 64) then
						if (Enum <= 61) then
							if (Enum > 60) then
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
							elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 62) then
							Stk[Inst[2]] = Inst[3];
						elseif (Enum > 63) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						else
							local A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						end
					elseif (Enum <= 66) then
						if (Enum > 65) then
							if (Stk[Inst[2]] == Stk[Inst[4]]) then
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
					elseif (Enum <= 67) then
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 68) then
						VIP = Inst[3];
					else
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					end
				elseif (Enum <= 74) then
					if (Enum <= 71) then
						if (Enum > 70) then
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						else
							Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
						end
					elseif (Enum <= 72) then
						local A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					elseif (Enum > 73) then
						Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
					else
						Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
					end
				elseif (Enum <= 77) then
					if (Enum <= 75) then
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 76) then
						if (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum <= 78) then
					do
						return;
					end
				elseif (Enum > 79) then
					local A = Inst[2];
					do
						return Unpack(Stk, A, Top);
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
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!183Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403043Q0067616D65030A3Q0047657453657276696365030B3Q001EE854CD05F952CB3FFF4503043Q00BD569C2003093Q00517FCEC44275C5CB5E03043Q00851D269C030D3Q00B6669C93AC6D8F94CB49BBA88B03043Q00C7E523C803083Q006973666F6C646572030A3Q006D616B65666F6C64657203013Q002F03043Q005341564503043Q004C4F414403063Q0052454D4F5645004A3Q0012293Q00013Q0020405Q0002001229000100013Q002040000100010003001229000200013Q002040000200020004001229000300053Q0006210003000A000100010004133Q000A0001001229000300063Q002040000400030007001229000500083Q002040000500050009001229000600083Q00204000060006000A00061400073Q000100062Q00073Q00064Q00078Q00073Q00044Q00073Q00014Q00073Q00024Q00073Q00053Q0012290008000B3Q00200900080008000C2Q000F000A00073Q00122B000B000D3Q00122B000C000E4Q0034000A000C4Q002000083Q00022Q000F000900073Q00122B000A000F3Q00122B000B00104Q001D0009000B00022Q000F000A00073Q00122B000B00113Q00122B000C00124Q001D000A000C00022Q0027000B5Q001229000C00134Q000F000D00094Q0035000C00020002000621000C002E000100010004133Q002E0001001229000C00144Q000F000D00094Q0039000C000200012Q000F000C00093Q00122B000D00154Q000F000E000A4Q0010000C000C000E000614000D0001000100022Q00073Q000C4Q00073Q00083Q000614000E0002000100022Q00073Q000C4Q00073Q00084Q000F000F000D4Q0017000F0001000200061400100003000100032Q00073Q000E4Q00073Q000F4Q00073Q00073Q001023000B0016001000061400100004000100022Q00073Q00074Q00073Q000F3Q001023000B0017001000061400100005000100032Q00073Q00074Q00073Q000F4Q00073Q000E3Q001023000B001800102Q003B000B00024Q004E3Q00013Q00063Q00023Q00026Q00F03F026Q00704002264Q002700025Q00122B000300014Q000C00045Q00122B000500013Q0004010003002100012Q000B00076Q000F000800024Q000B000900014Q000B000A00024Q000B000B00034Q000B000C00044Q000F000D6Q000F000E00063Q002032000F000600012Q0034000C000F4Q0020000B3Q00022Q000B000C00034Q000B000D00044Q000F000E00014Q000C000F00014Q0022000F0006000F001012000F0001000F2Q000C001000014Q00220010000600100010120010000100100020320010001000012Q0034000D00104Q000E000C6Q0020000A3Q000200203A000A000A00022Q004F0009000A4Q004C00073Q000100042Q0003000500012Q000B000300054Q000F000400024Q0025000300044Q005000036Q004E3Q00017Q00043Q0003063Q00697366696C65028Q0003083Q007265616466696C65030A3Q004A534F4E4465636F646500173Q0012293Q00014Q000B00016Q00353Q000200020006433Q001400013Q0004133Q0014000100122B3Q00024Q0004000100013Q00261E3Q0007000100020004133Q00070001001229000200034Q000B00036Q00350002000200022Q000F000100024Q000B000200013Q0020090002000200042Q000F000400014Q0025000200044Q005000025Q0004133Q000700010004133Q001600012Q00278Q003B3Q00024Q004E3Q00017Q00023Q0003093Q00777269746566696C65030A3Q004A534F4E456E636F646501083Q001229000100014Q000B00026Q000B000300013Q0020090003000300022Q000F00056Q0034000300054Q004C00013Q00012Q004E3Q00017Q000C3Q00028Q00026Q00F03F03063Q00747970656F6603063Q003B076675261403043Q001C48731403063Q00270DADD8D18A03073Q00BC5479DFB1BFED03063Q00CFAE5BCB84D303053Q00E1A1DB36A903053Q00652Q726F7203493Q00793E4324454B3E10395B355C5660101B503C094F2F432415274C023B10234137404C3D10315B2109543B5C2550654457294470572009437A4324472C47457A5F22152B5C4F3855221B03073Q005A305035452922022F3Q00122B000200013Q00261E00020007000100020004133Q000700012Q000B00036Q000B000400014Q00390003000200010004133Q002E000100261E00020001000100010004133Q00010001001229000300034Q000F00046Q00350003000200022Q000B000400023Q00122B000500043Q00122B000600054Q001D00040006000200064D00030024000100040004133Q00240001001229000300034Q000F000400014Q00350003000200022Q000B000400023Q00122B000500063Q00122B000600074Q001D00040006000200063C0003002A000100040004133Q002A0001001229000300034Q000F000400014Q00350003000200022Q000B000400023Q00122B000500083Q00122B000600094Q001D00040006000200063C0003002A000100040004133Q002A00010012290003000A4Q000B000400023Q00122B0005000B3Q00122B0006000C4Q0034000400064Q004C00033Q00012Q000B000300014Q004400033Q000100122B000200023Q0004133Q000100012Q004E3Q00017Q00073Q00028Q0003063Q00747970656F6603063Q0038A8D1DEFD2C03053Q00934BDCA3B703053Q00652Q726F7203243Q0003D714BB870B2E990BB49B173E8342918E1B6AD417A99F4228DC42BBCB113ECB0BB48C4C03063Q00624AB962DAEB01173Q00122B000100013Q00261E00010001000100010004133Q00010001001229000200024Q000F00036Q00350002000200022Q000B00035Q00122B000400033Q00122B000500044Q001D00030005000200063C00020012000100030004133Q00120001001229000200054Q000B00035Q00122B000400063Q00122B000500074Q0034000300054Q004C00023Q00012Q000B000200014Q0008000200024Q003B000200023Q0004133Q000100012Q004E3Q00017Q00093Q00028Q0003063Q00747970656F6603063Q00B9DF2Q2E17AD03053Q0079CAAB5C4703053Q00652Q726F7203243Q007B863FC020D756C820CF3CCB46D269EA29C712853CD2389E508D69C06CCD469A20CF2B9003063Q00BE32E849A14C00026Q00F03F011D3Q00122B000100013Q00261E00010015000100010004133Q00150001001229000200024Q000F00036Q00350002000200022Q000B00035Q00122B000400033Q00122B000500044Q001D00030005000200063C00020012000100030004133Q00120001001229000200054Q000B00035Q00122B000400063Q00122B000500074Q0034000300054Q004C00023Q00012Q000B000200013Q00204600023Q000800122B000100093Q00261E00010001000100090004133Q000100012Q000B000200024Q000B000300014Q00390002000200010004133Q001C00010004133Q000100012Q004E3Q00017Q00", GetFEnv(), ...);
