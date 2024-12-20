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
				if (Enum <= 28) then
					if (Enum <= 13) then
						if (Enum <= 6) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum == 1) then
									local A = Inst[2];
									local T = Stk[A];
									local B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									Stk[Inst[2]] = #Stk[Inst[3]];
								end
							elseif (Enum <= 4) then
								if (Enum == 3) then
									Stk[Inst[2]] = #Stk[Inst[3]];
								else
									local A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
								end
							elseif (Enum == 5) then
								do
									return Stk[Inst[2]];
								end
							else
								Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
							end
						elseif (Enum <= 9) then
							if (Enum <= 7) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							elseif (Enum > 8) then
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
						elseif (Enum <= 11) then
							if (Enum > 10) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 12) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 20) then
						if (Enum <= 16) then
							if (Enum <= 14) then
								Stk[Inst[2]] = Inst[3];
							elseif (Enum == 15) then
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
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum <= 18) then
							if (Enum > 17) then
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
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum > 19) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 24) then
						if (Enum <= 22) then
							if (Enum == 21) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 23) then
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
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
					elseif (Enum <= 26) then
						if (Enum == 25) then
							local A = Inst[2];
							local T = Stk[A];
							local B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						end
					elseif (Enum > 27) then
						do
							return;
						end
					else
						local A = Inst[2];
						do
							return Unpack(Stk, A, Top);
						end
					end
				elseif (Enum <= 42) then
					if (Enum <= 35) then
						if (Enum <= 31) then
							if (Enum <= 29) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 30) then
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							else
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Inst[3] do
									Insert(T, Stk[Idx]);
								end
							end
						elseif (Enum <= 33) then
							if (Enum == 32) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]];
							end
						elseif (Enum > 34) then
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
					elseif (Enum <= 38) then
						if (Enum <= 36) then
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
						elseif (Enum > 37) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 40) then
						if (Enum > 39) then
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
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
					elseif (Enum > 41) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
					end
				elseif (Enum <= 49) then
					if (Enum <= 45) then
						if (Enum <= 43) then
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
						elseif (Enum == 44) then
							Stk[Inst[2]] = {};
						else
							do
								return Stk[Inst[2]];
							end
						end
					elseif (Enum <= 47) then
						if (Enum > 46) then
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						else
							Stk[Inst[2]] = Inst[3] + Stk[Inst[4]];
						end
					elseif (Enum == 48) then
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
							if (Mvm[1] == 16) then
								Indexes[Idx - 1] = {Stk,Mvm[3]};
							else
								Indexes[Idx - 1] = {Upvalues,Mvm[3]};
							end
							Lupvals[#Lupvals + 1] = Indexes;
						end
						Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
					else
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 53) then
					if (Enum <= 51) then
						if (Enum == 50) then
							if not Stk[Inst[2]] then
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
					elseif (Enum == 52) then
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					else
						do
							return;
						end
					end
				elseif (Enum <= 55) then
					if (Enum > 54) then
						Stk[Inst[2]] = Inst[3];
					else
						local A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Top));
					end
				elseif (Enum == 56) then
					Stk[Inst[2]] = Upvalues[Inst[3]];
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
						if (Mvm[1] == 16) then
							Indexes[Idx - 1] = {Stk,Mvm[3]};
						else
							Indexes[Idx - 1] = {Upvalues,Mvm[3]};
						end
						Lupvals[#Lupvals + 1] = Indexes;
					end
					Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!4A3Q0003063Q00737472696E6703043Q006368617203043Q00627974652Q033Q0073756203053Q0062697433322Q033Q0062697403043Q0062786F7203053Q007461626C6503063Q00636F6E63617403063Q00696E7365727403023Q00D8C703083Q007EB1A3BB4586DBA703053Q00709C7994AE03053Q009C43AD4AA503043Q003AB6441303073Q002654D72976DC46030C3Q0071142B1EF7440F6225FF420503053Q009E3076427203043Q00BF3D003303073Q009BCB44705613C503073Q0076CF33F1496DE803083Q009826BD569C20188503063Q00EF54B54FEC4303043Q00269C37C7034D3Q00A0696838002EB50CBA7C6B66147DEE4BBD7F693B1666F94CA6697926073AF94CA53250310175A812FB2C330C1672FB56A4695B291E71AB70AB6F7538073BF742A173333B1066F353BC33703D1203083Q0023C81D1C4873149A03023Q0010BB03073Q005479DFB1BFED4C03063Q00E9059DF56C0703083Q00A1DB36A9C05A305003043Q0047430D2003043Q0045292260030E3Q0098C6D10B1727A883F00B0F2EFC9103063Q004BDCA3B76A6203043Q0016A39B3203053Q00B962DAEB5703073Q00EF3921E7CBA6DF03063Q00CAAB5C4786BE03063Q003AC23E8139D503043Q00E849A14C034D3Q00B3CD564D0DE1960D4F1FAC9745540AB3CC40480DBECB415210AFDC4C4950B8D64F1232A2CB430F4FE8880D791BBDD857510A9CD84F584C88DA50540EAF964F5C17B596515E0CB2C9561312AED803053Q007EDBB9223D03023Q0005CA03083Q00876CAE3E121E179303063Q00E5BD7F9D4FF603083Q00A7D6894AAB78CE5303043Q0085F13F5803063Q00C7EB90523D98030E3Q003704BC260E03B46B2017B42E2Q4703043Q004B6776D903043Q00D34D601103063Q007EA7341074D903073Q00F83C258DBD0CF103073Q009CA84E40E0D47903063Q0014EDB7C717FA03043Q00AE678EC5034D3Q005E3C4B283604B7193A5E2F6B59F142204A3A304DFD442B5036315BF642665C372811D44F3A5E6A740DA919184D3D2857ED5B0F5E35200FCB553A56283111F557215177365DEA5F384B76294BF903073Q009836483F58453E03023Q00DDC003043Q003CB4A48E030A4Q000C537975BA440E075103073Q0072383E6549478D03043Q00B6E8D6C103043Q00A4D889BB03103Q00E2F434BFAFEB0692C130BFA3BE2AE5B403073Q006BB28651D2C69E03043Q002C1792C303053Q00CA586EE2A603073Q00F31D87FAC3D60203053Q00AAA36FE29703063Q000233A0315E2303073Q00497150D2582E57035D3Q008938D902F4DB638200E69662CA1BF38939CF07F4843ECE1DE99529C306A98223C05DCB983ECC40B6D27D823EDEB30D8200E2873F821AE28028DE5DEA8025C35DD6B915C603D2A83A9831FF8263F51ECAA32DE924C4A80FC718A98D39CC03053Q0087E14CAD7200AE3Q00120D3Q00013Q00200B5Q000200120D000100013Q00200B00010001000300120D000200013Q00200B00020002000400120D000300053Q0006160003000A000100010004253Q000A000100120D000300063Q00200B00040003000700120D000500083Q00200B00050005000900120D000600083Q00200B00060006000A00063900073Q000100062Q00103Q00064Q00108Q00103Q00044Q00103Q00014Q00103Q00024Q00103Q00054Q002C000800044Q002C00093Q00042Q0021000A00073Q001237000B000B3Q001237000C000C4Q002A000A000C00022Q0021000B00073Q001237000C000D3Q001237000D000E4Q002A000B000D00022Q002F0009000A000B2Q0021000A00073Q001237000B000F3Q001237000C00104Q002A000A000C00022Q0021000B00073Q001237000C00113Q001237000D00124Q002A000B000D00022Q002F0009000A000B2Q0021000A00073Q001237000B00133Q001237000C00144Q002A000A000C00022Q0021000B00073Q001237000C00153Q001237000D00164Q002A000B000D00022Q002F0009000A000B2Q0021000A00073Q001237000B00173Q001237000C00184Q002A000A000C00022Q0021000B00073Q001237000C00193Q001237000D001A4Q002A000B000D00022Q002F0009000A000B2Q002C000A3Q00042Q0021000B00073Q001237000C001B3Q001237000D001C4Q002A000B000D00022Q0021000C00073Q001237000D001D3Q001237000E001E4Q002A000C000E00022Q002F000A000B000C2Q0021000B00073Q001237000C001F3Q001237000D00204Q002A000B000D00022Q0021000C00073Q001237000D00213Q001237000E00224Q002A000C000E00022Q002F000A000B000C2Q0021000B00073Q001237000C00233Q001237000D00244Q002A000B000D00022Q0021000C00073Q001237000D00253Q001237000E00264Q002A000C000E00022Q002F000A000B000C2Q0021000B00073Q001237000C00273Q001237000D00284Q002A000B000D00022Q0021000C00073Q001237000D00293Q001237000E002A4Q002A000C000E00022Q002F000A000B000C2Q002C000B3Q00042Q0021000C00073Q001237000D002B3Q001237000E002C4Q002A000C000E00022Q0021000D00073Q001237000E002D3Q001237000F002E4Q002A000D000F00022Q002F000B000C000D2Q0021000C00073Q001237000D002F3Q001237000E00304Q002A000C000E00022Q0021000D00073Q001237000E00313Q001237000F00324Q002A000D000F00022Q002F000B000C000D2Q0021000C00073Q001237000D00333Q001237000E00344Q002A000C000E00022Q0021000D00073Q001237000E00353Q001237000F00364Q002A000D000F00022Q002F000B000C000D2Q0021000C00073Q001237000D00373Q001237000E00384Q002A000C000E00022Q0021000D00073Q001237000E00393Q001237000F003A4Q002A000D000F00022Q002F000B000C000D2Q002C000C3Q00042Q0021000D00073Q001237000E003B3Q001237000F003C4Q002A000D000F00022Q0021000E00073Q001237000F003D3Q0012370010003E4Q002A000E001000022Q002F000C000D000E2Q0021000D00073Q001237000E003F3Q001237000F00404Q002A000D000F00022Q0021000E00073Q001237000F00413Q001237001000424Q002A000E001000022Q002F000C000D000E2Q0021000D00073Q001237000E00433Q001237000F00444Q002A000D000F00022Q0021000E00073Q001237000F00453Q001237001000464Q002A000E001000022Q002F000C000D000E2Q0021000D00073Q001237000E00473Q001237000F00484Q002A000D000F00022Q0021000E00073Q001237000F00493Q0012370010004A4Q002A000E001000022Q002F000C000D000E2Q00190008000400012Q0005000800024Q00353Q00013Q00013Q00023Q00026Q00F03F026Q00704002264Q002C00025Q001237000300014Q000300045Q001237000500013Q00040F0003002100012Q000900076Q0021000800024Q0009000900014Q0009000A00024Q0009000B00034Q0009000C00044Q0021000D6Q0021000E00063Q002028000F000600012Q0018000C000F4Q001D000B3Q00022Q0009000C00034Q0009000D00044Q0021000E00014Q0003000F00014Q0029000F0006000F00102E000F0001000F2Q0003001000014Q002900100006001000102E0010000100100020280010001000012Q0018000D00104Q0014000C6Q001D000A3Q000200201F000A000A00022Q00260009000A4Q003600073Q00010004120003000500012Q0009000300054Q0021000400024Q0020000300044Q001700036Q00353Q00017Q00", GetFEnv(), ...);
