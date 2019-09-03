def sbbq1 : instruction :=
  definst "sbbq" $ do
    pattern fun (v_3260 : imm int) (v_3262 : reg (bv 64)) => do
      v_8662 <- getRegister cf;
      v_8664 <- eval (handleImmediateWithSignExtend v_3260 32 32);
      v_8666 <- eval (mi 64 (svalueMInt v_8664));
      v_8670 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8666 (mi (bitwidthMInt v_8666) -1)));
      v_8673 <- getRegister v_3262;
      v_8675 <- eval (add (mux (eq v_8662 (expression.bv_nat 1 1)) v_8670 (add v_8670 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_8673));
      v_8680 <- eval (extract v_8675 1 2);
      v_8686 <- eval (extract v_8675 1 65);
      v_8690 <- eval (extract v_8666 0 1);
      v_8694 <- eval (eq (bv_xor v_8690 (mi (bitwidthMInt v_8690) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3262) v_8686;
      setRegister of (mux (bit_and (eq v_8694 (eq (extract v_8673 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8694 (eq v_8680 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8675 57 65));
      setRegister zf (zeroFlag v_8686);
      setRegister af (bv_xor (bv_xor (extract v_8664 27 28) (extract v_8673 59 60)) (extract v_8675 60 61));
      setRegister sf v_8680;
      setRegister cf (mux (notBool_ (eq (extract v_8675 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3270 : reg (bv 64)) (v_3271 : reg (bv 64)) => do
      v_8714 <- getRegister cf;
      v_8716 <- getRegister v_3270;
      v_8720 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8716 (mi (bitwidthMInt v_8716) -1)));
      v_8723 <- getRegister v_3271;
      v_8725 <- eval (add (mux (eq v_8714 (expression.bv_nat 1 1)) v_8720 (add v_8720 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_8723));
      v_8730 <- eval (extract v_8725 1 2);
      v_8735 <- eval (extract v_8725 1 65);
      v_8739 <- eval (extract v_8716 0 1);
      v_8743 <- eval (eq (bv_xor v_8739 (mi (bitwidthMInt v_8739) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3271) v_8735;
      setRegister of (mux (bit_and (eq v_8743 (eq (extract v_8723 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8743 (eq v_8730 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8725 57 65));
      setRegister zf (zeroFlag v_8735);
      setRegister af (bv_xor (extract (bv_xor v_8716 v_8723) 59 60) (extract v_8725 60 61));
      setRegister sf v_8730;
      setRegister cf (mux (notBool_ (eq (extract v_8725 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3263 : Mem) (v_3266 : reg (bv 64)) => do
      v_13337 <- getRegister cf;
      v_13339 <- evaluateAddress v_3263;
      v_13340 <- load v_13339 8;
      v_13344 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13340 (mi (bitwidthMInt v_13340) -1)));
      v_13347 <- getRegister v_3266;
      v_13349 <- eval (add (mux (eq v_13337 (expression.bv_nat 1 1)) v_13344 (add v_13344 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_13347));
      v_13354 <- eval (extract v_13349 1 2);
      v_13359 <- eval (extract v_13349 1 65);
      v_13363 <- eval (extract v_13340 0 1);
      v_13367 <- eval (eq (bv_xor v_13363 (mi (bitwidthMInt v_13363) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3266) v_13359;
      setRegister of (mux (bit_and (eq v_13367 (eq (extract v_13347 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13367 (eq v_13354 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13349 57 65));
      setRegister zf (zeroFlag v_13359);
      setRegister af (bv_xor (extract (bv_xor v_13340 v_13347) 59 60) (extract v_13349 60 61));
      setRegister sf v_13354;
      setRegister cf (mux (notBool_ (eq (extract v_13349 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3253 : imm int) (v_3250 : Mem) => do
      v_17970 <- evaluateAddress v_3250;
      v_17971 <- getRegister cf;
      v_17973 <- eval (handleImmediateWithSignExtend v_3253 32 32);
      v_17975 <- eval (mi 64 (svalueMInt v_17973));
      v_17979 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17975 (mi (bitwidthMInt v_17975) -1)));
      v_17982 <- load v_17970 8;
      v_17984 <- eval (add (mux (eq v_17971 (expression.bv_nat 1 1)) v_17979 (add v_17979 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_17982));
      v_17985 <- eval (extract v_17984 1 65);
      store v_17970 v_17985 8;
      v_17991 <- eval (extract v_17984 1 2);
      v_18000 <- eval (extract v_17975 0 1);
      v_18004 <- eval (eq (bv_xor v_18000 (mi (bitwidthMInt v_18000) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_18004 (eq (extract v_17982 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_18004 (eq v_17991 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_17984 57 65));
      setRegister af (bv_xor (bv_xor (extract v_17973 27 28) (extract v_17982 59 60)) (extract v_17984 60 61));
      setRegister zf (zeroFlag v_17985);
      setRegister sf v_17991;
      setRegister cf (mux (notBool_ (eq (extract v_17984 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3257 : reg (bv 64)) (v_3254 : Mem) => do
      v_18019 <- evaluateAddress v_3254;
      v_18020 <- getRegister cf;
      v_18022 <- getRegister v_3257;
      v_18026 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_18022 (mi (bitwidthMInt v_18022) -1)));
      v_18029 <- load v_18019 8;
      v_18031 <- eval (add (mux (eq v_18020 (expression.bv_nat 1 1)) v_18026 (add v_18026 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_18029));
      v_18032 <- eval (extract v_18031 1 65);
      store v_18019 v_18032 8;
      v_18038 <- eval (extract v_18031 1 2);
      v_18046 <- eval (extract v_18022 0 1);
      v_18050 <- eval (eq (bv_xor v_18046 (mi (bitwidthMInt v_18046) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_18050 (eq (extract v_18029 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_18050 (eq v_18038 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_18031 57 65));
      setRegister af (bv_xor (extract (bv_xor v_18022 v_18029) 59 60) (extract v_18031 60 61));
      setRegister zf (zeroFlag v_18032);
      setRegister sf v_18038;
      setRegister cf (mux (notBool_ (eq (extract v_18031 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
