def vinsertps1 : instruction :=
  definst "vinsertps" $ do
    pattern fun (v_2494 : imm int) (v_2491 : reg (bv 128)) (v_2492 : reg (bv 128)) (v_2493 : reg (bv 128)) => do
      v_4591 <- eval (handleImmediateWithSignExtend v_2494 8 8);
      v_4594 <- eval (extract v_4591 2 4);
      v_4595 <- eval (eq v_4594 (expression.bv_nat 2 0));
      v_4596 <- getRegister v_2492;
      v_4597 <- eval (extract v_4596 0 32);
      v_4598 <- eval (eq v_4594 (expression.bv_nat 2 1));
      v_4599 <- eval (eq v_4594 (expression.bv_nat 2 2));
      v_4600 <- eval (extract v_4591 0 2);
      v_4602 <- getRegister v_2491;
      v_4611 <- eval (mux (eq v_4600 (expression.bv_nat 2 0)) (extract v_4602 96 128) (mux (eq v_4600 (expression.bv_nat 2 1)) (extract v_4602 64 96) (mux (eq v_4600 (expression.bv_nat 2 2)) (extract v_4602 32 64) (extract v_4602 0 32))));
      v_4618 <- eval (extract v_4596 32 64);
      v_4626 <- eval (extract v_4596 64 96);
      setRegister (lhs.of_reg v_2493) (concat (concat (concat (mux (eq (extract v_4591 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4595 v_4597 (mux v_4598 v_4597 (mux v_4599 v_4597 v_4611)))) (mux (eq (extract v_4591 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4595 v_4618 (mux v_4598 v_4618 (mux v_4599 v_4611 v_4618))))) (mux (eq (extract v_4591 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4595 v_4626 (mux v_4598 v_4611 v_4626)))) (mux (eq (extract v_4591 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_4595 v_4611 (extract v_4596 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2488 : imm int) (v_2485 : Mem) (v_2486 : reg (bv 128)) (v_2487 : reg (bv 128)) => do
      v_10634 <- eval (handleImmediateWithSignExtend v_2488 8 8);
      v_10637 <- eval (extract v_10634 2 4);
      v_10638 <- eval (eq v_10637 (expression.bv_nat 2 0));
      v_10639 <- getRegister v_2486;
      v_10640 <- eval (extract v_10639 0 32);
      v_10641 <- eval (eq v_10637 (expression.bv_nat 2 1));
      v_10642 <- eval (eq v_10637 (expression.bv_nat 2 2));
      v_10643 <- evaluateAddress v_2485;
      v_10644 <- load v_10643 4;
      v_10651 <- eval (extract v_10639 32 64);
      v_10659 <- eval (extract v_10639 64 96);
      setRegister (lhs.of_reg v_2487) (concat (concat (concat (mux (eq (extract v_10634 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_10638 v_10640 (mux v_10641 v_10640 (mux v_10642 v_10640 v_10644)))) (mux (eq (extract v_10634 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_10638 v_10651 (mux v_10641 v_10651 (mux v_10642 v_10644 v_10651))))) (mux (eq (extract v_10634 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_10638 v_10659 (mux v_10641 v_10644 v_10659)))) (mux (eq (extract v_10634 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_10638 v_10644 (extract v_10639 96 128))));
      pure ()
    pat_end
