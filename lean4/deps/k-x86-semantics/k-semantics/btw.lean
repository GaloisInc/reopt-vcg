def btw1 : instruction :=
  definst "btw" $ do
    pattern fun (v_3231 : imm int) (v_3233 : reg (bv 16)) => do
      v_6647 <- getRegister v_3233;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6647 (uvalueMInt (mi 16 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3231 8 8) (expression.bv_nat 8 15)))))) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3237 : reg (bv 16)) (v_3238 : reg (bv 16)) => do
      v_6660 <- getRegister v_3238;
      v_6661 <- getRegister v_3237;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6660 (uvalueMInt (mi 16 (svalueMInt (bv_and v_6661 (expression.bv_nat 16 15)))))) 15 16);
      pure ()
    pat_end;
    pattern fun (v_3224 : imm int) (v_3223 : Mem) => do
      v_10070 <- evaluateAddress v_3223;
      v_10071 <- eval (handleImmediateWithSignExtend v_3224 8 8);
      v_10076 <- load (add v_10070 (concat (expression.bv_nat 59 0) (bv_and (extract v_10071 0 5) (expression.bv_nat 5 1)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_10076 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_10071 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3228 : reg (bv 16)) (v_3227 : Mem) => do
      v_10088 <- evaluateAddress v_3227;
      v_10089 <- getRegister v_3228;
      v_10094 <- load (add v_10088 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_10089 64) 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_10094 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_10089 13 16)))) 7 8);
      pure ()
    pat_end
