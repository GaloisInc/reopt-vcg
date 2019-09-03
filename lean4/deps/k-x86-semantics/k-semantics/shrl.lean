def shrl1 : instruction :=
  definst "shrl" $ do
    pattern fun cl (v_2928 : reg (bv 32)) => do
      v_5932 <- getRegister rcx;
      v_5934 <- eval (bv_and (extract v_5932 56 64) (expression.bv_nat 8 31));
      v_5935 <- eval (uge v_5934 (expression.bv_nat 8 32));
      v_5938 <- eval (eq v_5934 (expression.bv_nat 8 0));
      v_5939 <- eval (notBool_ v_5938);
      v_5940 <- getRegister v_2928;
      v_5944 <- eval (lshr (concat v_5940 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_5934)));
      v_5948 <- getRegister cf;
      v_5958 <- getRegister sf;
      v_5963 <- eval (bit_and v_5939 undef);
      v_5964 <- getRegister af;
      v_5969 <- eval (extract v_5944 0 32);
      v_5972 <- getRegister zf;
      v_6007 <- getRegister pf;
      v_6012 <- eval (eq v_5934 (expression.bv_nat 8 1));
      v_6017 <- getRegister of;
      setRegister (lhs.of_reg v_2928) v_5969;
      setRegister of (mux (bit_or (bit_and v_6012 (eq (extract v_5940 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6012) (bit_or v_5963 (bit_and v_5938 (eq v_6017 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_5939 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_5944 31 32) (expression.bv_nat 1 1)) (eq (extract v_5944 30 31) (expression.bv_nat 1 1)))) (eq (extract v_5944 29 30) (expression.bv_nat 1 1)))) (eq (extract v_5944 28 29) (expression.bv_nat 1 1)))) (eq (extract v_5944 27 28) (expression.bv_nat 1 1)))) (eq (extract v_5944 26 27) (expression.bv_nat 1 1)))) (eq (extract v_5944 25 26) (expression.bv_nat 1 1)))) (eq (extract v_5944 24 25) (expression.bv_nat 1 1)))) (bit_and v_5938 (eq v_6007 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_5939 (eq v_5969 (expression.bv_nat 32 0))) (bit_and v_5938 (eq v_5972 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_5963 (bit_and v_5938 (eq v_5964 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_5939 (eq (extract v_5944 0 1) (expression.bv_nat 1 1))) (bit_and v_5938 (eq v_5958 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5935 undef) (bit_and (notBool_ v_5935) (bit_or (bit_and v_5939 (eq (extract v_5944 32 33) (expression.bv_nat 1 1))) (bit_and v_5938 (eq v_5948 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2931 : imm int) (v_2933 : reg (bv 32)) => do
      v_6032 <- eval (bv_and (handleImmediateWithSignExtend v_2931 8 8) (expression.bv_nat 8 31));
      v_6033 <- eval (uge v_6032 (expression.bv_nat 8 32));
      v_6036 <- eval (eq v_6032 (expression.bv_nat 8 0));
      v_6037 <- eval (notBool_ v_6036);
      v_6038 <- getRegister v_2933;
      v_6042 <- eval (lshr (concat v_6038 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_6032)));
      v_6046 <- getRegister cf;
      v_6056 <- getRegister sf;
      v_6061 <- eval (bit_and v_6037 undef);
      v_6062 <- getRegister af;
      v_6067 <- eval (extract v_6042 0 32);
      v_6070 <- getRegister zf;
      v_6105 <- getRegister pf;
      v_6110 <- eval (eq v_6032 (expression.bv_nat 8 1));
      v_6115 <- getRegister of;
      setRegister (lhs.of_reg v_2933) v_6067;
      setRegister of (mux (bit_or (bit_and v_6110 (eq (extract v_6038 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_6110) (bit_or v_6061 (bit_and v_6036 (eq v_6115 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_6037 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_6042 31 32) (expression.bv_nat 1 1)) (eq (extract v_6042 30 31) (expression.bv_nat 1 1)))) (eq (extract v_6042 29 30) (expression.bv_nat 1 1)))) (eq (extract v_6042 28 29) (expression.bv_nat 1 1)))) (eq (extract v_6042 27 28) (expression.bv_nat 1 1)))) (eq (extract v_6042 26 27) (expression.bv_nat 1 1)))) (eq (extract v_6042 25 26) (expression.bv_nat 1 1)))) (eq (extract v_6042 24 25) (expression.bv_nat 1 1)))) (bit_and v_6036 (eq v_6105 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_6037 (eq v_6067 (expression.bv_nat 32 0))) (bit_and v_6036 (eq v_6070 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_6061 (bit_and v_6036 (eq v_6062 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_6037 (eq (extract v_6042 0 1) (expression.bv_nat 1 1))) (bit_and v_6036 (eq v_6056 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_6033 undef) (bit_and (notBool_ v_6033) (bit_or (bit_and v_6037 (eq (extract v_6042 32 33) (expression.bv_nat 1 1))) (bit_and v_6036 (eq v_6046 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2940 : reg (bv 32)) => do
      v_6131 <- getRegister v_2940;
      v_6133 <- eval (lshr (concat v_6131 (expression.bv_nat 1 0)) 1);
      v_6136 <- eval (extract v_6133 0 32);
      setRegister (lhs.of_reg v_2940) v_6136;
      setRegister of (extract v_6131 0 1);
      setRegister pf (parityFlag (extract v_6133 24 32));
      setRegister zf (zeroFlag v_6136);
      setRegister af undef;
      setRegister sf (extract v_6133 0 1);
      setRegister cf (extract v_6133 32 33);
      pure ()
    pat_end;
    pattern fun (v_2936 : reg (bv 32)) => do
      v_8001 <- getRegister v_2936;
      v_8003 <- eval (lshr (concat v_8001 (expression.bv_nat 1 0)) 1);
      v_8010 <- eval (extract v_8003 0 32);
      setRegister (lhs.of_reg v_2936) v_8010;
      setRegister of (mux (eq (extract v_8001 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8003 24 32));
      setRegister zf (zeroFlag v_8010);
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (eq (extract v_8003 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_8003 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2936 : reg (bv 32)) => do
      v_8024 <- getRegister v_2936;
      v_8026 <- eval (lshr (concat v_8024 (expression.bv_nat 1 0)) 1);
      v_8029 <- eval (extract v_8026 0 32);
      setRegister (lhs.of_reg v_2936) v_8029;
      setRegister of (extract v_8024 0 1);
      setRegister pf (parityFlag (extract v_8026 24 32));
      setRegister zf (zeroFlag v_8029);
      setRegister af undef;
      setRegister sf (extract v_8026 0 1);
      setRegister cf (extract v_8026 32 33);
      pure ()
    pat_end;
    pattern fun cl (v_2914 : Mem) => do
      v_12148 <- evaluateAddress v_2914;
      v_12149 <- load v_12148 4;
      v_12151 <- getRegister rcx;
      v_12153 <- eval (bv_and (extract v_12151 56 64) (expression.bv_nat 8 31));
      v_12156 <- eval (lshr (concat v_12149 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_12153)));
      v_12157 <- eval (extract v_12156 0 32);
      store v_12148 v_12157 4;
      v_12159 <- eval (uge v_12153 (expression.bv_nat 8 32));
      v_12162 <- eval (eq v_12153 (expression.bv_nat 8 0));
      v_12163 <- eval (notBool_ v_12162);
      v_12167 <- getRegister cf;
      v_12177 <- getRegister sf;
      v_12184 <- getRegister zf;
      v_12189 <- eval (bit_and v_12163 undef);
      v_12190 <- getRegister af;
      v_12225 <- getRegister pf;
      v_12230 <- eval (eq v_12153 (expression.bv_nat 8 1));
      v_12235 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12230 (eq (extract v_12149 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12230) (bit_or v_12189 (bit_and v_12162 (eq v_12235 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12163 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12156 31 32) (expression.bv_nat 1 1)) (eq (extract v_12156 30 31) (expression.bv_nat 1 1)))) (eq (extract v_12156 29 30) (expression.bv_nat 1 1)))) (eq (extract v_12156 28 29) (expression.bv_nat 1 1)))) (eq (extract v_12156 27 28) (expression.bv_nat 1 1)))) (eq (extract v_12156 26 27) (expression.bv_nat 1 1)))) (eq (extract v_12156 25 26) (expression.bv_nat 1 1)))) (eq (extract v_12156 24 25) (expression.bv_nat 1 1)))) (bit_and v_12162 (eq v_12225 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12189 (bit_and v_12162 (eq v_12190 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12163 (eq v_12157 (expression.bv_nat 32 0))) (bit_and v_12162 (eq v_12184 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12163 (eq (extract v_12156 0 1) (expression.bv_nat 1 1))) (bit_and v_12162 (eq v_12177 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12159 undef) (bit_and (notBool_ v_12159) (bit_or (bit_and v_12163 (eq (extract v_12156 32 33) (expression.bv_nat 1 1))) (bit_and v_12162 (eq v_12167 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2917 : imm int) (v_2918 : Mem) => do
      v_12248 <- evaluateAddress v_2918;
      v_12249 <- load v_12248 4;
      v_12252 <- eval (bv_and (handleImmediateWithSignExtend v_2917 8 8) (expression.bv_nat 8 31));
      v_12255 <- eval (lshr (concat v_12249 (expression.bv_nat 1 0)) (uvalueMInt (concat (expression.bv_nat 25 0) v_12252)));
      v_12256 <- eval (extract v_12255 0 32);
      store v_12248 v_12256 4;
      v_12258 <- eval (uge v_12252 (expression.bv_nat 8 32));
      v_12261 <- eval (eq v_12252 (expression.bv_nat 8 0));
      v_12262 <- eval (notBool_ v_12261);
      v_12266 <- getRegister cf;
      v_12276 <- getRegister sf;
      v_12283 <- getRegister zf;
      v_12288 <- eval (bit_and v_12262 undef);
      v_12289 <- getRegister af;
      v_12324 <- getRegister pf;
      v_12329 <- eval (eq v_12252 (expression.bv_nat 8 1));
      v_12334 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_12329 (eq (extract v_12249 0 1) (expression.bv_nat 1 1))) (bit_and (notBool_ v_12329) (bit_or v_12288 (bit_and v_12261 (eq v_12334 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_12262 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_12255 31 32) (expression.bv_nat 1 1)) (eq (extract v_12255 30 31) (expression.bv_nat 1 1)))) (eq (extract v_12255 29 30) (expression.bv_nat 1 1)))) (eq (extract v_12255 28 29) (expression.bv_nat 1 1)))) (eq (extract v_12255 27 28) (expression.bv_nat 1 1)))) (eq (extract v_12255 26 27) (expression.bv_nat 1 1)))) (eq (extract v_12255 25 26) (expression.bv_nat 1 1)))) (eq (extract v_12255 24 25) (expression.bv_nat 1 1)))) (bit_and v_12261 (eq v_12324 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_12288 (bit_and v_12261 (eq v_12289 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_12262 (eq v_12256 (expression.bv_nat 32 0))) (bit_and v_12261 (eq v_12283 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_12262 (eq (extract v_12255 0 1) (expression.bv_nat 1 1))) (bit_and v_12261 (eq v_12276 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_12258 undef) (bit_and (notBool_ v_12258) (bit_or (bit_and v_12262 (eq (extract v_12255 32 33) (expression.bv_nat 1 1))) (bit_and v_12261 (eq v_12266 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) => do
      v_13411 <- evaluateAddress v_2921;
      v_13412 <- load v_13411 4;
      v_13414 <- eval (lshr (concat v_13412 (expression.bv_nat 1 0)) 1);
      v_13415 <- eval (extract v_13414 0 32);
      store v_13411 v_13415 4;
      setRegister of (mux (eq (extract v_13412 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13414 24 32));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_13415);
      setRegister sf (mux (eq (extract v_13414 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_13414 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) => do
      v_13435 <- evaluateAddress v_2921;
      v_13436 <- load v_13435 4;
      v_13438 <- eval (lshr (concat v_13436 (expression.bv_nat 1 0)) 1);
      v_13439 <- eval (extract v_13438 0 32);
      store v_13435 v_13439 4;
      setRegister of (extract v_13436 0 1);
      setRegister pf (parityFlag (extract v_13438 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_13439);
      setRegister sf (extract v_13438 0 1);
      setRegister cf (extract v_13438 32 33);
      pure ()
    pat_end
