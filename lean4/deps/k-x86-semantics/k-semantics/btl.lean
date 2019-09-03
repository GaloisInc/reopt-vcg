def btl1 : instruction :=
  definst "btl" $ do
    pattern fun (v_3087 : imm int) (v_3089 : reg (bv 32)) => do
      v_6321 <- getRegister v_3089;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6321 (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3087 8 8) (expression.bv_nat 8 31)))))) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3093 : reg (bv 32)) (v_3094 : reg (bv 32)) => do
      v_6334 <- getRegister v_3094;
      v_6335 <- getRegister v_3093;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6334 (uvalueMInt (mi 32 (svalueMInt (bv_and v_6335 (expression.bv_nat 32 31)))))) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3080 : imm int) (v_3079 : Mem) => do
      v_9989 <- evaluateAddress v_3079;
      v_9990 <- eval (handleImmediateWithSignExtend v_3080 8 8);
      v_9995 <- load (add v_9989 (concat (expression.bv_nat 59 0) (bv_and (extract v_9990 0 5) (expression.bv_nat 5 3)))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_9995 (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_9990 5 8) (expression.bv_nat 3 7))))) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3084 : reg (bv 32)) (v_3083 : Mem) => do
      v_10007 <- evaluateAddress v_3083;
      v_10008 <- getRegister v_3084;
      v_10013 <- load (add v_10007 (concat (expression.bv_nat 3 0) (extract (leanSignExtend v_10008 64) 0 61))) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_10013 (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_10008 29 32)))) 7 8);
      pure ()
    pat_end
