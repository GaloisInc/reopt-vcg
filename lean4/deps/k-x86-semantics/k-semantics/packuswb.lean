def packuswb1 : instruction :=
  definst "packuswb" $ do
    pattern fun (v_3165 : reg (bv 128)) (v_3166 : reg (bv 128)) => do
      v_5500 <- getRegister v_3165;
      v_5501 <- eval (extract v_5500 0 16);
      v_5507 <- eval (extract v_5500 16 32);
      v_5513 <- eval (extract v_5500 32 48);
      v_5519 <- eval (extract v_5500 48 64);
      v_5525 <- eval (extract v_5500 64 80);
      v_5531 <- eval (extract v_5500 80 96);
      v_5537 <- eval (extract v_5500 96 112);
      v_5543 <- eval (extract v_5500 112 128);
      v_5549 <- getRegister v_3166;
      v_5550 <- eval (extract v_5549 0 16);
      v_5556 <- eval (extract v_5549 16 32);
      v_5562 <- eval (extract v_5549 32 48);
      v_5568 <- eval (extract v_5549 48 64);
      v_5574 <- eval (extract v_5549 64 80);
      v_5580 <- eval (extract v_5549 80 96);
      v_5586 <- eval (extract v_5549 96 112);
      v_5592 <- eval (extract v_5549 112 128);
      setRegister (lhs.of_reg v_3166) (concat (mux (sgt v_5501 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5501 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 8 16))) (concat (mux (sgt v_5507 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5507 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 24 32))) (concat (mux (sgt v_5513 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5513 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 40 48))) (concat (mux (sgt v_5519 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5519 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 56 64))) (concat (mux (sgt v_5525 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5525 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 72 80))) (concat (mux (sgt v_5531 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5531 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 88 96))) (concat (mux (sgt v_5537 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5537 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 104 112))) (concat (mux (sgt v_5543 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5543 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5500 120 128))) (concat (mux (sgt v_5550 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5550 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 8 16))) (concat (mux (sgt v_5556 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5556 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 24 32))) (concat (mux (sgt v_5562 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5562 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 40 48))) (concat (mux (sgt v_5568 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5568 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 56 64))) (concat (mux (sgt v_5574 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5574 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 72 80))) (concat (mux (sgt v_5580 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5580 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 88 96))) (concat (mux (sgt v_5586 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5586 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 104 112))) (mux (sgt v_5592 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5592 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5549 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3160 : Mem) (v_3161 : reg (bv 128)) => do
      v_9438 <- evaluateAddress v_3160;
      v_9439 <- load v_9438 16;
      v_9440 <- eval (extract v_9439 0 16);
      v_9446 <- eval (extract v_9439 16 32);
      v_9452 <- eval (extract v_9439 32 48);
      v_9458 <- eval (extract v_9439 48 64);
      v_9464 <- eval (extract v_9439 64 80);
      v_9470 <- eval (extract v_9439 80 96);
      v_9476 <- eval (extract v_9439 96 112);
      v_9482 <- eval (extract v_9439 112 128);
      v_9488 <- getRegister v_3161;
      v_9489 <- eval (extract v_9488 0 16);
      v_9495 <- eval (extract v_9488 16 32);
      v_9501 <- eval (extract v_9488 32 48);
      v_9507 <- eval (extract v_9488 48 64);
      v_9513 <- eval (extract v_9488 64 80);
      v_9519 <- eval (extract v_9488 80 96);
      v_9525 <- eval (extract v_9488 96 112);
      v_9531 <- eval (extract v_9488 112 128);
      setRegister (lhs.of_reg v_3161) (concat (mux (sgt v_9440 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9440 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 8 16))) (concat (mux (sgt v_9446 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9446 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 24 32))) (concat (mux (sgt v_9452 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9452 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 40 48))) (concat (mux (sgt v_9458 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9458 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 56 64))) (concat (mux (sgt v_9464 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9464 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 72 80))) (concat (mux (sgt v_9470 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9470 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 88 96))) (concat (mux (sgt v_9476 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9476 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 104 112))) (concat (mux (sgt v_9482 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9482 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9439 120 128))) (concat (mux (sgt v_9489 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9489 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 8 16))) (concat (mux (sgt v_9495 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9495 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 24 32))) (concat (mux (sgt v_9501 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9501 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 40 48))) (concat (mux (sgt v_9507 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9507 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 56 64))) (concat (mux (sgt v_9513 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9513 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 72 80))) (concat (mux (sgt v_9519 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9519 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 88 96))) (concat (mux (sgt v_9525 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9525 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 104 112))) (mux (sgt v_9531 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9531 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9488 120 128))))))))))))))))));
      pure ()
    pat_end
