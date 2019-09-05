def rcrl1 : instruction :=
  definst "rcrl" $ do
    pattern fun cl (v_2555 : reg (bv 32)) => do
      v_4432 <- getRegister rcx;
      v_4436 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_4432 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4437 <- eval (extract v_4436 25 33);
      v_4438 <- eval (eq v_4437 (expression.bv_nat 8 1));
      v_4439 <- getRegister cf;
      v_4442 <- getRegister v_2555;
      v_4444 <- eval (ror (concat (mux (eq v_4439 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4442) v_4436);
      v_4451 <- eval (eq v_4437 (expression.bv_nat 8 0));
      v_4454 <- getRegister of;
      setRegister (lhs.of_reg v_2555) (extract v_4444 1 33);
      setRegister cf (isBitSet v_4444 0);
      setRegister of (bit_or (bit_and v_4438 (notBool_ (eq (isBitSet v_4444 1) (isBitSet v_4444 2)))) (bit_and (notBool_ v_4438) (bit_or (bit_and (notBool_ v_4451) undef) (bit_and v_4451 (eq v_4454 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2558 : imm int) (v_2560 : reg (bv 32)) => do
      v_4468 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2558 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4469 <- eval (extract v_4468 25 33);
      v_4470 <- eval (eq v_4469 (expression.bv_nat 8 1));
      v_4471 <- getRegister cf;
      v_4474 <- getRegister v_2560;
      v_4476 <- eval (ror (concat (mux (eq v_4471 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4474) v_4468);
      v_4483 <- eval (eq v_4469 (expression.bv_nat 8 0));
      v_4486 <- getRegister of;
      setRegister (lhs.of_reg v_2560) (extract v_4476 1 33);
      setRegister cf (isBitSet v_4476 0);
      setRegister of (bit_or (bit_and v_4470 (notBool_ (eq (isBitSet v_4476 1) (isBitSet v_4476 2)))) (bit_and (notBool_ v_4470) (bit_or (bit_and (notBool_ v_4483) undef) (bit_and v_4483 (eq v_4486 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2544 : Mem) => do
      v_11915 <- evaluateAddress v_2544;
      v_11916 <- getRegister cf;
      v_11919 <- load v_11915 4;
      v_11921 <- getRegister rcx;
      v_11925 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_11921 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_11926 <- eval (ror (concat (mux (eq v_11916 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11919) v_11925);
      store v_11915 (extract v_11926 1 33) 4;
      v_11929 <- eval (extract v_11925 25 33);
      v_11930 <- eval (eq v_11929 (expression.bv_nat 8 1));
      v_11937 <- eval (eq v_11929 (expression.bv_nat 8 0));
      v_11940 <- getRegister of;
      setRegister cf (isBitSet v_11926 0);
      setRegister of (bit_or (bit_and v_11930 (notBool_ (eq (isBitSet v_11926 1) (isBitSet v_11926 2)))) (bit_and (notBool_ v_11930) (bit_or (bit_and (notBool_ v_11937) undef) (bit_and v_11937 (eq v_11940 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2547 : imm int) (v_2548 : Mem) => do
      v_11949 <- evaluateAddress v_2548;
      v_11950 <- getRegister cf;
      v_11953 <- load v_11949 4;
      v_11958 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2547 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_11959 <- eval (ror (concat (mux (eq v_11950 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11953) v_11958);
      store v_11949 (extract v_11959 1 33) 4;
      v_11962 <- eval (extract v_11958 25 33);
      v_11963 <- eval (eq v_11962 (expression.bv_nat 8 1));
      v_11970 <- eval (eq v_11962 (expression.bv_nat 8 0));
      v_11973 <- getRegister of;
      setRegister cf (isBitSet v_11959 0);
      setRegister of (bit_or (bit_and v_11963 (notBool_ (eq (isBitSet v_11959 1) (isBitSet v_11959 2)))) (bit_and (notBool_ v_11963) (bit_or (bit_and (notBool_ v_11970) undef) (bit_and v_11970 (eq v_11973 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
