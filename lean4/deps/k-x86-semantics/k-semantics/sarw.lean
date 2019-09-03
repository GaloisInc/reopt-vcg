def sarw1 : instruction :=
  definst "sarw" $ do
    pattern fun cl (v_3126 : reg (bv 16)) => do
      v_7920 <- getRegister rcx;
      v_7922 <- eval (bv_and (extract v_7920 56 64) (expression.bv_nat 8 31));
      v_7923 <- eval (eq v_7922 (expression.bv_nat 8 0));
      v_7924 <- eval (notBool_ v_7923);
      v_7925 <- getRegister v_3126;
      v_7931 <- eval (ashr (mi 17 (svalueMInt (concat v_7925 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 9 0) v_7922)));
      v_7935 <- getRegister cf;
      v_7943 <- getRegister sf;
      v_7948 <- eval (bit_and v_7924 undef);
      v_7949 <- getRegister af;
      v_7954 <- eval (extract v_7931 0 16);
      v_7957 <- getRegister zf;
      v_7992 <- getRegister pf;
      v_7999 <- getRegister of;
      setRegister (lhs.of_reg v_3126) v_7954;
      setRegister of (mux (bit_and (notBool_ (eq v_7922 (expression.bv_nat 8 1))) (bit_or v_7948 (bit_and v_7923 (eq v_7999 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7924 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7931 15 16) (expression.bv_nat 1 1)) (eq (extract v_7931 14 15) (expression.bv_nat 1 1)))) (eq (extract v_7931 13 14) (expression.bv_nat 1 1)))) (eq (extract v_7931 12 13) (expression.bv_nat 1 1)))) (eq (extract v_7931 11 12) (expression.bv_nat 1 1)))) (eq (extract v_7931 10 11) (expression.bv_nat 1 1)))) (eq (extract v_7931 9 10) (expression.bv_nat 1 1)))) (eq (extract v_7931 8 9) (expression.bv_nat 1 1)))) (bit_and v_7923 (eq v_7992 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7924 (eq v_7954 (expression.bv_nat 16 0))) (bit_and v_7923 (eq v_7957 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7948 (bit_and v_7923 (eq v_7949 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7924 (eq (extract v_7931 0 1) (expression.bv_nat 1 1))) (bit_and v_7923 (eq v_7943 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7924 (eq (extract v_7931 16 17) (expression.bv_nat 1 1))) (bit_and v_7923 (eq v_7935 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3129 : imm int) (v_3131 : reg (bv 16)) => do
      v_8013 <- eval (bv_and (handleImmediateWithSignExtend v_3129 8 8) (expression.bv_nat 8 31));
      v_8014 <- eval (eq v_8013 (expression.bv_nat 8 0));
      v_8015 <- eval (notBool_ v_8014);
      v_8016 <- getRegister v_3131;
      v_8022 <- eval (ashr (mi 17 (svalueMInt (concat v_8016 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 9 0) v_8013)));
      v_8026 <- getRegister cf;
      v_8034 <- getRegister sf;
      v_8039 <- eval (bit_and v_8015 undef);
      v_8040 <- getRegister af;
      v_8045 <- eval (extract v_8022 0 16);
      v_8048 <- getRegister zf;
      v_8083 <- getRegister pf;
      v_8090 <- getRegister of;
      setRegister (lhs.of_reg v_3131) v_8045;
      setRegister of (mux (bit_and (notBool_ (eq v_8013 (expression.bv_nat 8 1))) (bit_or v_8039 (bit_and v_8014 (eq v_8090 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_8015 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_8022 15 16) (expression.bv_nat 1 1)) (eq (extract v_8022 14 15) (expression.bv_nat 1 1)))) (eq (extract v_8022 13 14) (expression.bv_nat 1 1)))) (eq (extract v_8022 12 13) (expression.bv_nat 1 1)))) (eq (extract v_8022 11 12) (expression.bv_nat 1 1)))) (eq (extract v_8022 10 11) (expression.bv_nat 1 1)))) (eq (extract v_8022 9 10) (expression.bv_nat 1 1)))) (eq (extract v_8022 8 9) (expression.bv_nat 1 1)))) (bit_and v_8014 (eq v_8083 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_8015 (eq v_8045 (expression.bv_nat 16 0))) (bit_and v_8014 (eq v_8048 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_8039 (bit_and v_8014 (eq v_8040 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_8015 (eq (extract v_8022 0 1) (expression.bv_nat 1 1))) (bit_and v_8014 (eq v_8034 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_8015 (eq (extract v_8022 16 17) (expression.bv_nat 1 1))) (bit_and v_8014 (eq v_8026 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3138 : reg (bv 16)) => do
      v_8105 <- getRegister v_3138;
      v_8109 <- eval (ashr (mi 17 (svalueMInt (concat v_8105 (expression.bv_nat 1 0)))) 1);
      v_8112 <- eval (extract v_8109 0 16);
      setRegister (lhs.of_reg v_3138) v_8112;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8109 8 16));
      setRegister zf (zeroFlag v_8112);
      setRegister af undef;
      setRegister sf (extract v_8109 0 1);
      setRegister cf (extract v_8109 16 17);
      pure ()
    pat_end;
    pattern fun (v_3134 : reg (bv 16)) => do
      v_9897 <- getRegister v_3134;
      v_9901 <- eval (ashr (mi 17 (svalueMInt (concat v_9897 (expression.bv_nat 1 0)))) 1);
      v_9908 <- eval (extract v_9901 0 16);
      setRegister (lhs.of_reg v_3134) v_9908;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9901 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9908);
      setRegister sf (mux (eq (extract v_9901 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9901 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3134 : reg (bv 16)) => do
      v_9919 <- getRegister v_3134;
      v_9923 <- eval (ashr (mi 17 (svalueMInt (concat v_9919 (expression.bv_nat 1 0)))) 1);
      v_9926 <- eval (extract v_9923 0 16);
      setRegister (lhs.of_reg v_3134) v_9926;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9923 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_9926);
      setRegister sf (extract v_9923 0 1);
      setRegister cf (extract v_9923 16 17);
      pure ()
    pat_end;
    pattern fun cl (v_3112 : Mem) => do
      v_17220 <- evaluateAddress v_3112;
      v_17221 <- load v_17220 2;
      v_17225 <- getRegister rcx;
      v_17227 <- eval (bv_and (extract v_17225 56 64) (expression.bv_nat 8 31));
      v_17230 <- eval (ashr (mi 17 (svalueMInt (concat v_17221 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 9 0) v_17227)));
      v_17231 <- eval (extract v_17230 0 16);
      store v_17220 v_17231 2;
      v_17233 <- eval (eq v_17227 (expression.bv_nat 8 0));
      v_17234 <- eval (notBool_ v_17233);
      v_17238 <- getRegister cf;
      v_17246 <- getRegister sf;
      v_17253 <- getRegister zf;
      v_17258 <- eval (bit_and v_17234 undef);
      v_17259 <- getRegister af;
      v_17294 <- getRegister pf;
      v_17301 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17227 (expression.bv_nat 8 1))) (bit_or v_17258 (bit_and v_17233 (eq v_17301 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17234 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17230 15 16) (expression.bv_nat 1 1)) (eq (extract v_17230 14 15) (expression.bv_nat 1 1)))) (eq (extract v_17230 13 14) (expression.bv_nat 1 1)))) (eq (extract v_17230 12 13) (expression.bv_nat 1 1)))) (eq (extract v_17230 11 12) (expression.bv_nat 1 1)))) (eq (extract v_17230 10 11) (expression.bv_nat 1 1)))) (eq (extract v_17230 9 10) (expression.bv_nat 1 1)))) (eq (extract v_17230 8 9) (expression.bv_nat 1 1)))) (bit_and v_17233 (eq v_17294 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17258 (bit_and v_17233 (eq v_17259 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17234 (eq v_17231 (expression.bv_nat 16 0))) (bit_and v_17233 (eq v_17253 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17234 (eq (extract v_17230 0 1) (expression.bv_nat 1 1))) (bit_and v_17233 (eq v_17246 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17234 (eq (extract v_17230 16 17) (expression.bv_nat 1 1))) (bit_and v_17233 (eq v_17238 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3116 : imm int) (v_3115 : Mem) => do
      v_17313 <- evaluateAddress v_3115;
      v_17314 <- load v_17313 2;
      v_17319 <- eval (bv_and (handleImmediateWithSignExtend v_3116 8 8) (expression.bv_nat 8 31));
      v_17322 <- eval (ashr (mi 17 (svalueMInt (concat v_17314 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 9 0) v_17319)));
      v_17323 <- eval (extract v_17322 0 16);
      store v_17313 v_17323 2;
      v_17325 <- eval (eq v_17319 (expression.bv_nat 8 0));
      v_17326 <- eval (notBool_ v_17325);
      v_17330 <- getRegister cf;
      v_17338 <- getRegister sf;
      v_17345 <- getRegister zf;
      v_17350 <- eval (bit_and v_17326 undef);
      v_17351 <- getRegister af;
      v_17386 <- getRegister pf;
      v_17393 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17319 (expression.bv_nat 8 1))) (bit_or v_17350 (bit_and v_17325 (eq v_17393 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17326 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17322 15 16) (expression.bv_nat 1 1)) (eq (extract v_17322 14 15) (expression.bv_nat 1 1)))) (eq (extract v_17322 13 14) (expression.bv_nat 1 1)))) (eq (extract v_17322 12 13) (expression.bv_nat 1 1)))) (eq (extract v_17322 11 12) (expression.bv_nat 1 1)))) (eq (extract v_17322 10 11) (expression.bv_nat 1 1)))) (eq (extract v_17322 9 10) (expression.bv_nat 1 1)))) (eq (extract v_17322 8 9) (expression.bv_nat 1 1)))) (bit_and v_17325 (eq v_17386 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17350 (bit_and v_17325 (eq v_17351 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17326 (eq v_17323 (expression.bv_nat 16 0))) (bit_and v_17325 (eq v_17345 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17326 (eq (extract v_17322 0 1) (expression.bv_nat 1 1))) (bit_and v_17325 (eq v_17338 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17326 (eq (extract v_17322 16 17) (expression.bv_nat 1 1))) (bit_and v_17325 (eq v_17330 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) => do
      v_18235 <- evaluateAddress v_3119;
      v_18236 <- load v_18235 2;
      v_18240 <- eval (ashr (mi 17 (svalueMInt (concat v_18236 (expression.bv_nat 1 0)))) 1);
      v_18241 <- eval (extract v_18240 0 16);
      store v_18235 v_18241 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18240 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18241);
      setRegister sf (mux (eq (extract v_18240 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18240 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3119 : Mem) => do
      v_18258 <- evaluateAddress v_3119;
      v_18259 <- load v_18258 2;
      v_18263 <- eval (ashr (mi 17 (svalueMInt (concat v_18259 (expression.bv_nat 1 0)))) 1);
      v_18264 <- eval (extract v_18263 0 16);
      store v_18258 v_18264 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18263 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_18264);
      setRegister sf (extract v_18263 0 1);
      setRegister cf (extract v_18263 16 17);
      pure ()
    pat_end
