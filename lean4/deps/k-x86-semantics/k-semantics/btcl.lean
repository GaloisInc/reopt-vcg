def btcl1 : instruction :=
  definst "btcl" $ do
    pattern fun (v_3019 : imm int) (v_3022 : reg (bv 32)) => do
      v_6040 <- getRegister v_3022;
      v_6045 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3019 8 8) (expression.bv_nat 8 31)))));
      setRegister (lhs.of_reg v_3022) (bv_xor v_6040 (extract (shl (expression.bv_nat 32 1) v_6045) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6040 v_6045) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3026 : reg (bv 32)) (v_3027 : reg (bv 32)) => do
      v_6057 <- getRegister v_3027;
      v_6058 <- getRegister v_3026;
      v_6062 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6058 (expression.bv_nat 32 31)))));
      setRegister (lhs.of_reg v_3027) (bv_xor v_6057 (extract (shl (expression.bv_nat 32 1) v_6062) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6057 v_6062) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3011 : imm int) (v_3013 : Mem) => do
      v_11050 <- evaluateAddress v_3013;
      v_11051 <- eval (handleImmediateWithSignExtend v_3011 8 8);
      v_11055 <- eval (add v_11050 (concat (expression.bv_nat 59 0) (bv_and (extract v_11051 0 5) (expression.bv_nat 5 3))));
      v_11056 <- load v_11055 1;
      v_11060 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11051 5 8) (expression.bv_nat 3 7))));
      store v_11055 (bv_xor v_11056 (extract (shl (expression.bv_nat 8 1) v_11060) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11056 v_11060) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3017 : reg (bv 32)) (v_3016 : Mem) => do
      v_11072 <- evaluateAddress v_3016;
      v_11073 <- getRegister v_3017;
      v_11078 <- eval (add v_11072 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11073)) 0 61)));
      v_11079 <- load v_11078 1;
      v_11082 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11073 29 32)));
      store v_11078 (bv_xor v_11079 (extract (shl (expression.bv_nat 8 1) v_11082) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11079 v_11082) 7 8);
      pure ()
    pat_end
