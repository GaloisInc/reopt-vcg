def insertps1 : instruction :=
  definst "insertps" $ do
    pattern fun (v_3018 : imm int) (v_3021 : reg (bv 128)) (v_3022 : reg (bv 128)) => do
      v_5689 <- eval (handleImmediateWithSignExtend v_3018 8 8);
      v_5692 <- eval (extract v_5689 2 4);
      v_5693 <- eval (eq v_5692 (expression.bv_nat 2 0));
      v_5694 <- getRegister v_3022;
      v_5695 <- eval (extract v_5694 0 32);
      v_5696 <- eval (eq v_5692 (expression.bv_nat 2 1));
      v_5697 <- eval (eq v_5692 (expression.bv_nat 2 2));
      v_5698 <- eval (extract v_5689 0 2);
      v_5700 <- getRegister v_3021;
      v_5709 <- eval (mux (eq v_5698 (expression.bv_nat 2 0)) (extract v_5700 96 128) (mux (eq v_5698 (expression.bv_nat 2 1)) (extract v_5700 64 96) (mux (eq v_5698 (expression.bv_nat 2 2)) (extract v_5700 32 64) (extract v_5700 0 32))));
      v_5716 <- eval (extract v_5694 32 64);
      v_5724 <- eval (extract v_5694 64 96);
      setRegister (lhs.of_reg v_3022) (concat (concat (concat (mux (eq (extract v_5689 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5693 v_5695 (mux v_5696 v_5695 (mux v_5697 v_5695 v_5709)))) (mux (eq (extract v_5689 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5693 v_5716 (mux v_5696 v_5716 (mux v_5697 v_5709 v_5716))))) (mux (eq (extract v_5689 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5693 v_5724 (mux v_5696 v_5709 v_5724)))) (mux (eq (extract v_5689 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_5693 v_5709 (extract v_5694 96 128))));
      pure ()
    pat_end;
    pattern fun (v_3013 : imm int) (v_3014 : Mem) (v_3016 : reg (bv 128)) => do
      v_9468 <- eval (handleImmediateWithSignExtend v_3013 8 8);
      v_9471 <- eval (extract v_9468 2 4);
      v_9472 <- eval (eq v_9471 (expression.bv_nat 2 0));
      v_9473 <- getRegister v_3016;
      v_9474 <- eval (extract v_9473 0 32);
      v_9475 <- eval (eq v_9471 (expression.bv_nat 2 1));
      v_9476 <- eval (eq v_9471 (expression.bv_nat 2 2));
      v_9477 <- evaluateAddress v_3014;
      v_9478 <- load v_9477 4;
      v_9485 <- eval (extract v_9473 32 64);
      v_9493 <- eval (extract v_9473 64 96);
      setRegister (lhs.of_reg v_3016) (concat (concat (concat (mux (eq (extract v_9468 4 5) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9472 v_9474 (mux v_9475 v_9474 (mux v_9476 v_9474 v_9478)))) (mux (eq (extract v_9468 5 6) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9472 v_9485 (mux v_9475 v_9485 (mux v_9476 v_9478 v_9485))))) (mux (eq (extract v_9468 6 7) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9472 v_9493 (mux v_9475 v_9478 v_9493)))) (mux (eq (extract v_9468 7 8) (expression.bv_nat 1 1)) (expression.bv_nat 32 0) (mux v_9472 v_9478 (extract v_9473 96 128))));
      pure ()
    pat_end
