def btcq1 : instruction :=
  definst "btcq" $ do
    pattern fun (v_3037 : imm int) (v_3040 : reg (bv 64)) => do
      v_6082 <- getRegister v_3040;
      v_6087 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3037 8 8) (expression.bv_nat 8 63)))));
      setRegister (lhs.of_reg v_3040) (bv_xor v_6082 (extract (shl (expression.bv_nat 64 1) v_6087) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6082 v_6087) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3044 : reg (bv 64)) (v_3045 : reg (bv 64)) => do
      v_6099 <- getRegister v_3045;
      v_6100 <- getRegister v_3044;
      v_6104 <- eval (uvalueMInt (mi 64 (svalueMInt (bv_and v_6100 (expression.bv_nat 64 63)))));
      setRegister (lhs.of_reg v_3045) (bv_xor v_6099 (extract (shl (expression.bv_nat 64 1) v_6104) 0 64));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6099 v_6104) 63 64);
      pure ()
    pat_end;
    pattern fun (v_3029 : imm int) (v_3031 : Mem) => do
      v_11094 <- evaluateAddress v_3031;
      v_11095 <- eval (handleImmediateWithSignExtend v_3029 8 8);
      v_11099 <- eval (add v_11094 (concat (expression.bv_nat 59 0) (bv_and (extract v_11095 0 5) (expression.bv_nat 5 7))));
      v_11100 <- load v_11099 1;
      v_11104 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11095 5 8) (expression.bv_nat 3 7))));
      store v_11099 (bv_xor v_11100 (extract (shl (expression.bv_nat 8 1) v_11104) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11100 v_11104) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3035 : reg (bv 64)) (v_3034 : Mem) => do
      v_11116 <- evaluateAddress v_3034;
      v_11117 <- getRegister v_3035;
      v_11120 <- eval (add v_11116 (concat (expression.bv_nat 3 0) (extract v_11117 0 61)));
      v_11121 <- load v_11120 1;
      v_11124 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11117 61 64)));
      store v_11120 (bv_xor v_11121 (extract (shl (expression.bv_nat 8 1) v_11124) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11121 v_11124) 7 8);
      pure ()
    pat_end
