def psubsw1 : instruction :=
  definst "psubsw" $ do
    pattern fun (v_3117 : reg (bv 128)) (v_3118 : reg (bv 128)) => do
      v_8601 <- getRegister v_3118;
      v_8605 <- getRegister v_3117;
      v_8609 <- eval (sub (mi 18 (svalueMInt (extract v_8601 0 16))) (mi 18 (svalueMInt (extract v_8605 0 16))));
      v_8621 <- eval (sub (mi 18 (svalueMInt (extract v_8601 16 32))) (mi 18 (svalueMInt (extract v_8605 16 32))));
      v_8633 <- eval (sub (mi 18 (svalueMInt (extract v_8601 32 48))) (mi 18 (svalueMInt (extract v_8605 32 48))));
      v_8645 <- eval (sub (mi 18 (svalueMInt (extract v_8601 48 64))) (mi 18 (svalueMInt (extract v_8605 48 64))));
      v_8657 <- eval (sub (mi 18 (svalueMInt (extract v_8601 64 80))) (mi 18 (svalueMInt (extract v_8605 64 80))));
      v_8669 <- eval (sub (mi 18 (svalueMInt (extract v_8601 80 96))) (mi 18 (svalueMInt (extract v_8605 80 96))));
      v_8681 <- eval (sub (mi 18 (svalueMInt (extract v_8601 96 112))) (mi 18 (svalueMInt (extract v_8605 96 112))));
      v_8693 <- eval (sub (mi 18 (svalueMInt (extract v_8601 112 128))) (mi 18 (svalueMInt (extract v_8605 112 128))));
      setRegister (lhs.of_reg v_3118) (concat (mux (sgt v_8609 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8609 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8609 2 18))) (concat (mux (sgt v_8621 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8621 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8621 2 18))) (concat (mux (sgt v_8633 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8633 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8633 2 18))) (concat (mux (sgt v_8645 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8645 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8645 2 18))) (concat (mux (sgt v_8657 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8657 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8657 2 18))) (concat (mux (sgt v_8669 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8669 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8669 2 18))) (concat (mux (sgt v_8681 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8681 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8681 2 18))) (mux (sgt v_8693 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8693 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8693 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3112 : Mem) (v_3113 : reg (bv 128)) => do
      v_15506 <- getRegister v_3113;
      v_15510 <- evaluateAddress v_3112;
      v_15511 <- load v_15510 16;
      v_15515 <- eval (sub (mi 18 (svalueMInt (extract v_15506 0 16))) (mi 18 (svalueMInt (extract v_15511 0 16))));
      v_15527 <- eval (sub (mi 18 (svalueMInt (extract v_15506 16 32))) (mi 18 (svalueMInt (extract v_15511 16 32))));
      v_15539 <- eval (sub (mi 18 (svalueMInt (extract v_15506 32 48))) (mi 18 (svalueMInt (extract v_15511 32 48))));
      v_15551 <- eval (sub (mi 18 (svalueMInt (extract v_15506 48 64))) (mi 18 (svalueMInt (extract v_15511 48 64))));
      v_15563 <- eval (sub (mi 18 (svalueMInt (extract v_15506 64 80))) (mi 18 (svalueMInt (extract v_15511 64 80))));
      v_15575 <- eval (sub (mi 18 (svalueMInt (extract v_15506 80 96))) (mi 18 (svalueMInt (extract v_15511 80 96))));
      v_15587 <- eval (sub (mi 18 (svalueMInt (extract v_15506 96 112))) (mi 18 (svalueMInt (extract v_15511 96 112))));
      v_15599 <- eval (sub (mi 18 (svalueMInt (extract v_15506 112 128))) (mi 18 (svalueMInt (extract v_15511 112 128))));
      setRegister (lhs.of_reg v_3113) (concat (mux (sgt v_15515 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15515 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15515 2 18))) (concat (mux (sgt v_15527 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15527 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15527 2 18))) (concat (mux (sgt v_15539 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15539 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15539 2 18))) (concat (mux (sgt v_15551 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15551 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15551 2 18))) (concat (mux (sgt v_15563 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15563 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15563 2 18))) (concat (mux (sgt v_15575 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15575 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15575 2 18))) (concat (mux (sgt v_15587 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15587 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15587 2 18))) (mux (sgt v_15599 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15599 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15599 2 18))))))))));
      pure ()
    pat_end
