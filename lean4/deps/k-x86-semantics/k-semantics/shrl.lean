def shrl1 : instruction :=
  definst "shrl" $ do
    pattern fun cl (v_2915 : reg (bv 32)) => do
      v_5936 <- getRegister rcx;
      v_5938 <- eval (bv_and (extract v_5936 56 64) (expression.bv_nat 8 31));
      v_5939 <- eval (uge v_5938 (expression.bv_nat 8 32));
      v_5942 <- eval (eq v_5938 (expression.bv_nat 8 0));
      v_5943 <- eval (notBool_ v_5942);
      v_5944 <- getRegister v_2915;
      v_5948 <- eval (lshr (concat v_5944 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_5938)));
      v_5952 <- getRegister cf;
      v_5962 <- getRegister sf;
      v_5967 <- eval (extract v_5948 0 32);
      v_5970 <- getRegister zf;
      v_5975 <- eval (bit_and v_5943 undef);
      v_5976 <- getRegister af;
      v_6011 <- getRegister pf;
      v_6016 <- eval (eq v_5938 (expression.bv_nat 8 1));
      v_6021 <- getRegister of;
      setRegister (lhs.of_reg v_2915) v_5967;
      setRegister of (mux (bit_or (bit_and v_6016 (eq (extract v_5944 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6016) (bit_or v_5975 (bit_and v_5942 (eq v_6021 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5943 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5948 31 32) (expression.bv_nat 1 1)) (eq (extract v_5948 30 31) (expression.bv_nat 1 1)))) (eq (extract v_5948 29 30) (expression.bv_nat 1 1)))) (eq (extract v_5948 28 29) (expression.bv_nat 1 1)))) (eq (extract v_5948 27 28) (expression.bv_nat 1 1)))) (eq (extract v_5948 26 27) (expression.bv_nat 1 1)))) (eq (extract v_5948 25 26) (expression.bv_nat 1 1)))) (eq (extract v_5948 24 25) (expression.bv_nat 1 1)))) (bit_and v_5942 (eq v_6011 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5975 (bit_and v_5942 (eq v_5976 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5943 (eq v_5967 (expression.bv_nat 32 0))) (bit_and v_5942 (eq v_5970 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5943 (eq (extract v_5948 0 1) (expression.bv_nat 1 1))) (bit_and v_5942 (eq v_5962 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5939 undef) (bit_and (notBool_ v_5939) (bit_or (bit_and v_5943 (eq (extract v_5948 32 33) (expression.bv_nat 1 1))) (bit_and v_5942 (eq v_5952 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2918 : imm int) (v_2920 : reg (bv 32)) => do
      v_6036 <- eval (bv_and (handleImmediateWithSignExtend v_2918 8 8) (expression.bv_nat 8 31));
      v_6037 <- eval (uge v_6036 (expression.bv_nat 8 32));
      v_6040 <- eval (eq v_6036 (expression.bv_nat 8 0));
      v_6041 <- eval (notBool_ v_6040);
      v_6042 <- getRegister v_2920;
      v_6046 <- eval (lshr (concat v_6042 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_6036)));
      v_6050 <- getRegister cf;
      v_6060 <- getRegister sf;
      v_6065 <- eval (extract v_6046 0 32);
      v_6068 <- getRegister zf;
      v_6073 <- eval (bit_and v_6041 undef);
      v_6074 <- getRegister af;
      v_6109 <- getRegister pf;
      v_6114 <- eval (eq v_6036 (expression.bv_nat 8 1));
      v_6119 <- getRegister of;
      setRegister (lhs.of_reg v_2920) v_6065;
      setRegister of (mux (bit_or (bit_and v_6114 (eq (extract v_6042 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6114) (bit_or v_6073 (bit_and v_6040 (eq v_6119 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6041 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6046 31 32) (expression.bv_nat 1 1)) (eq (extract v_6046 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6046 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6046 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6046 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6046 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6046 25 26) (expression.bv_nat 1 1)))) (eq (extract v_6046 24 25) (expression.bv_nat 1 1)))) (bit_and v_6040 (eq v_6109 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6073 (bit_and v_6040 (eq v_6074 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6041 (eq v_6065 (expression.bv_nat 32 0))) (bit_and v_6040 (eq v_6068 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6041 (eq (extract v_6046 0 1) (expression.bv_nat 1 1))) (bit_and v_6040 (eq v_6060 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6037 undef) (bit_and (notBool_ v_6037) (bit_or (bit_and v_6041 (eq (extract v_6046 32 33) (expression.bv_nat 1 1))) (bit_and v_6040 (eq v_6050 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2927 : reg (bv 32)) => do
      v_6135 <- getRegister v_2927;
      v_6137 <- eval (lshr (concat v_6135 (expression.bv_nat 1 0)) 1);
      v_6140 <- eval (extract v_6137 0 32);
      setRegister (lhs.of_reg v_2927) v_6140;
      setRegister of (extract v_6135 0 1);
      setRegister pf (parityFlag (extract v_6137 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_6140);
      setRegister sf (extract v_6137 0 1);
      setRegister cf (extract v_6137 32 33);
      pure ()
    pat_end;
    pattern fun (v_2923 : reg (bv 32)) => do
      v_7977 <- getRegister v_2923;
      v_7979 <- eval (lshr (concat v_7977 (expression.bv_nat 1 0)) 1);
      v_7986 <- eval (extract v_7979 0 32);
      setRegister (lhs.of_reg v_2923) v_7986;
      setRegister of (mux (eq (extract v_7977 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7979 24 32));
      setRegister zf (zeroFlag v_7986);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_7979 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_7979 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2923 : reg (bv 32)) => do
      v_8000 <- getRegister v_2923;
      v_8002 <- eval (lshr (concat v_8000 (expression.bv_nat 1 0)) 1);
      v_8005 <- eval (extract v_8002 0 32);
      setRegister (lhs.of_reg v_2923) v_8005;
      setRegister of (extract v_8000 0 1);
      setRegister pf (parityFlag (extract v_8002 24 32));
      setRegister zf (zeroFlag v_8005);
      setRegister af undef;
      setRegister sf (extract v_8002 0 1);
      setRegister cf (extract v_8002 32 33);
      pure ()
    pat_end;
    pattern fun cl (v_2901 : Mem) => do
      v_12076 <- evaluateAddress v_2901;
      v_12077 <- load v_12076 4;
      v_12079 <- getRegister rcx;
      v_12081 <- eval (bv_and (extract v_12079 56 64) (expression.bv_nat 8 31));
      v_12084 <- eval (lshr (concat v_12077 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_12081)));
      v_12085 <- eval (extract v_12084 0 32);
      store v_12076 v_12085 4;
      v_12087 <- eval (uge v_12081 (expression.bv_nat 8 32));
      v_12090 <- eval (eq v_12081 (expression.bv_nat 8 0));
      v_12091 <- eval (notBool_ v_12090);
      v_12095 <- getRegister cf;
      v_12105 <- getRegister sf;
      v_12112 <- getRegister zf;
      v_12117 <- eval (bit_and v_12091 undef);
      v_12118 <- getRegister af;
      v_12153 <- getRegister pf;
      v_12158 <- eval (eq v_12081 (expression.bv_nat 8 1));
      v_12163 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12158 (eq (extract v_12077 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12158) (bit_or v_12117 (bit_and v_12090 (eq v_12163 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12091 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12084 31 32) (expression.bv_nat 1 1)) (eq (extract v_12084 30 31) (expression.bv_nat 1 1)))) (eq (extract v_12084 29 30) (expression.bv_nat 1 1)))) (eq (extract v_12084 28 29) (expression.bv_nat 1 1)))) (eq (extract v_12084 27 28) (expression.bv_nat 1 1)))) (eq (extract v_12084 26 27) (expression.bv_nat 1 1)))) (eq (extract v_12084 25 26) (expression.bv_nat 1 1)))) (eq (extract v_12084 24 25) (expression.bv_nat 1 1)))) (bit_and v_12090 (eq v_12153 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12117 (bit_and v_12090 (eq v_12118 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12091 (eq v_12085 (expression.bv_nat 32 0))) (bit_and v_12090 (eq v_12112 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12091 (eq (extract v_12084 0 1) (expression.bv_nat 1 1))) (bit_and v_12090 (eq v_12105 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12087 undef) (bit_and (notBool_ v_12087) (bit_or (bit_and v_12091 (eq (extract v_12084 32 33) (expression.bv_nat 1 1))) (bit_and v_12090 (eq v_12095 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2904 : imm int) (v_2905 : Mem) => do
      v_12176 <- evaluateAddress v_2905;
      v_12177 <- load v_12176 4;
      v_12180 <- eval (bv_and (handleImmediateWithSignExtend v_2904 8 8) (expression.bv_nat 8 31));
      v_12183 <- eval (lshr (concat v_12177 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_12180)));
      v_12184 <- eval (extract v_12183 0 32);
      store v_12176 v_12184 4;
      v_12186 <- eval (uge v_12180 (expression.bv_nat 8 32));
      v_12189 <- eval (eq v_12180 (expression.bv_nat 8 0));
      v_12190 <- eval (notBool_ v_12189);
      v_12194 <- getRegister cf;
      v_12204 <- getRegister sf;
      v_12211 <- getRegister zf;
      v_12216 <- eval (bit_and v_12190 undef);
      v_12217 <- getRegister af;
      v_12252 <- getRegister pf;
      v_12257 <- eval (eq v_12180 (expression.bv_nat 8 1));
      v_12262 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12257 (eq (extract v_12177 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12257) (bit_or v_12216 (bit_and v_12189 (eq v_12262 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12190 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12183 31 32) (expression.bv_nat 1 1)) (eq (extract v_12183 30 31) (expression.bv_nat 1 1)))) (eq (extract v_12183 29 30) (expression.bv_nat 1 1)))) (eq (extract v_12183 28 29) (expression.bv_nat 1 1)))) (eq (extract v_12183 27 28) (expression.bv_nat 1 1)))) (eq (extract v_12183 26 27) (expression.bv_nat 1 1)))) (eq (extract v_12183 25 26) (expression.bv_nat 1 1)))) (eq (extract v_12183 24 25) (expression.bv_nat 1 1)))) (bit_and v_12189 (eq v_12252 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12216 (bit_and v_12189 (eq v_12217 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12190 (eq v_12184 (expression.bv_nat 32 0))) (bit_and v_12189 (eq v_12211 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12190 (eq (extract v_12183 0 1) (expression.bv_nat 1 1))) (bit_and v_12189 (eq v_12204 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12186 undef) (bit_and (notBool_ v_12186) (bit_or (bit_and v_12190 (eq (extract v_12183 32 33) (expression.bv_nat 1 1))) (bit_and v_12189 (eq v_12194 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2908 : Mem) => do
      v_13376 <- evaluateAddress v_2908;
      v_13377 <- load v_13376 4;
      v_13379 <- eval (lshr (concat v_13377 (expression.bv_nat 1 0)) 1);
      v_13380 <- eval (extract v_13379 0 32);
      store v_13376 v_13380 4;
      setRegister of (mux (eq (extract v_13377 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13379 24 32));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13380);
      setRegister sf (mux (eq (extract v_13379 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13379 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2908 : Mem) => do
      v_13400 <- evaluateAddress v_2908;
      v_13401 <- load v_13400 4;
      v_13403 <- eval (lshr (concat v_13401 (expression.bv_nat 1 0)) 1);
      v_13404 <- eval (extract v_13403 0 32);
      store v_13400 v_13404 4;
      setRegister of (extract v_13401 0 1);
      setRegister pf (parityFlag (extract v_13403 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_13404);
      setRegister sf (extract v_13403 0 1);
      setRegister cf (extract v_13403 32 33);
      pure ()
    pat_end
