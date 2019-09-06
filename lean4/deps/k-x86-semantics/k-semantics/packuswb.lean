def packuswb1 : instruction :=
  definst "packuswb" $ do
    pattern fun (v_3190 : reg (bv 128)) (v_3191 : reg (bv 128)) => do
      v_5527 <- getRegister v_3190;
      v_5528 <- eval (extract v_5527 0 16);
      v_5534 <- eval (extract v_5527 16 32);
      v_5540 <- eval (extract v_5527 32 48);
      v_5546 <- eval (extract v_5527 48 64);
      v_5552 <- eval (extract v_5527 64 80);
      v_5558 <- eval (extract v_5527 80 96);
      v_5564 <- eval (extract v_5527 96 112);
      v_5570 <- eval (extract v_5527 112 128);
      v_5576 <- getRegister v_3191;
      v_5577 <- eval (extract v_5576 0 16);
      v_5583 <- eval (extract v_5576 16 32);
      v_5589 <- eval (extract v_5576 32 48);
      v_5595 <- eval (extract v_5576 48 64);
      v_5601 <- eval (extract v_5576 64 80);
      v_5607 <- eval (extract v_5576 80 96);
      v_5613 <- eval (extract v_5576 96 112);
      v_5619 <- eval (extract v_5576 112 128);
      setRegister (lhs.of_reg v_3191) (concat (mux (sgt v_5528 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5528 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 8 16))) (concat (mux (sgt v_5534 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5534 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 24 32))) (concat (mux (sgt v_5540 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5540 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 40 48))) (concat (mux (sgt v_5546 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5546 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 56 64))) (concat (mux (sgt v_5552 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5552 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 72 80))) (concat (mux (sgt v_5558 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5558 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 88 96))) (concat (mux (sgt v_5564 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5564 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 104 112))) (concat (mux (sgt v_5570 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5570 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5527 120 128))) (concat (mux (sgt v_5577 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5577 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 8 16))) (concat (mux (sgt v_5583 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5583 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 24 32))) (concat (mux (sgt v_5589 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5589 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 40 48))) (concat (mux (sgt v_5595 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5595 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 56 64))) (concat (mux (sgt v_5601 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5601 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 72 80))) (concat (mux (sgt v_5607 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5607 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 88 96))) (concat (mux (sgt v_5613 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5613 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 104 112))) (mux (sgt v_5619 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5619 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5576 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 128)) => do
      v_9465 <- evaluateAddress v_3186;
      v_9466 <- load v_9465 16;
      v_9467 <- eval (extract v_9466 0 16);
      v_9473 <- eval (extract v_9466 16 32);
      v_9479 <- eval (extract v_9466 32 48);
      v_9485 <- eval (extract v_9466 48 64);
      v_9491 <- eval (extract v_9466 64 80);
      v_9497 <- eval (extract v_9466 80 96);
      v_9503 <- eval (extract v_9466 96 112);
      v_9509 <- eval (extract v_9466 112 128);
      v_9515 <- getRegister v_3187;
      v_9516 <- eval (extract v_9515 0 16);
      v_9522 <- eval (extract v_9515 16 32);
      v_9528 <- eval (extract v_9515 32 48);
      v_9534 <- eval (extract v_9515 48 64);
      v_9540 <- eval (extract v_9515 64 80);
      v_9546 <- eval (extract v_9515 80 96);
      v_9552 <- eval (extract v_9515 96 112);
      v_9558 <- eval (extract v_9515 112 128);
      setRegister (lhs.of_reg v_3187) (concat (mux (sgt v_9467 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9467 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 8 16))) (concat (mux (sgt v_9473 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9473 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 24 32))) (concat (mux (sgt v_9479 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9479 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 40 48))) (concat (mux (sgt v_9485 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9485 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 56 64))) (concat (mux (sgt v_9491 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9491 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 72 80))) (concat (mux (sgt v_9497 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9497 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 88 96))) (concat (mux (sgt v_9503 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9503 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 104 112))) (concat (mux (sgt v_9509 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9509 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9466 120 128))) (concat (mux (sgt v_9516 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9516 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 8 16))) (concat (mux (sgt v_9522 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9522 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 24 32))) (concat (mux (sgt v_9528 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9528 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 40 48))) (concat (mux (sgt v_9534 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9534 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 56 64))) (concat (mux (sgt v_9540 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9540 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 72 80))) (concat (mux (sgt v_9546 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9546 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 88 96))) (concat (mux (sgt v_9552 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9552 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 104 112))) (mux (sgt v_9558 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9558 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9515 120 128))))))))))))))))));
      pure ()
    pat_end
