def btsl1 : instruction :=
  definst "btsl" $ do
    pattern fun (v_3163 : imm int) (v_3166 : reg (bv 32)) => do
      v_6378 <- getRegister v_3166;
      v_6383 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and (handleImmediateWithSignExtend v_3163 8 8) (expression.bv_nat 8 31)))));
      setRegister (lhs.of_reg v_3166) (bv_or v_6378 (extract (shl (expression.bv_nat 32 1) v_6383) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6378 v_6383) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3170 : reg (bv 32)) (v_3171 : reg (bv 32)) => do
      v_6395 <- getRegister v_3171;
      v_6396 <- getRegister v_3170;
      v_6400 <- eval (uvalueMInt (mi 32 (svalueMInt (bv_and v_6396 (expression.bv_nat 32 31)))));
      setRegister (lhs.of_reg v_3171) (bv_or v_6395 (extract (shl (expression.bv_nat 32 1) v_6400) 0 32));
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_6395 v_6400) 31 32);
      pure ()
    pat_end;
    pattern fun (v_3155 : imm int) (v_3157 : Mem) => do
      v_11328 <- evaluateAddress v_3157;
      v_11329 <- eval (handleImmediateWithSignExtend v_3155 8 8);
      v_11333 <- eval (add v_11328 (concat (expression.bv_nat 59 0) (bv_and (extract v_11329 0 5) (expression.bv_nat 5 3))));
      v_11334 <- load v_11333 1;
      v_11338 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (bv_and (extract v_11329 5 8) (expression.bv_nat 3 7))));
      store v_11333 (bv_or v_11334 (extract (shl (expression.bv_nat 8 1) v_11338) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11334 v_11338) 7 8);
      pure ()
    pat_end;
    pattern fun (v_3161 : reg (bv 32)) (v_3160 : Mem) => do
      v_11350 <- evaluateAddress v_3160;
      v_11351 <- getRegister v_3161;
      v_11356 <- eval (add v_11350 (concat (expression.bv_nat 3 0) (extract (mi 64 (svalueMInt v_11351)) 0 61)));
      v_11357 <- load v_11356 1;
      v_11360 <- eval (uvalueMInt (concat (expression.bv_nat 5 0) (extract v_11351 29 32)));
      store v_11356 (bv_or v_11357 (extract (shl (expression.bv_nat 8 1) v_11360) 0 8)) 1;
      setRegister of undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf (extract (lshr v_11357 v_11360) 7 8);
      pure ()
    pat_end
