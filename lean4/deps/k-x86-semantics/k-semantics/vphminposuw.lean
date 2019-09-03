def vphminposuw1 : instruction :=
  definst "vphminposuw" $ do
    pattern fun (v_3215 : reg (bv 128)) (v_3216 : reg (bv 128)) => do
      v_9456 <- getRegister v_3215;
      v_9457 <- eval (extract v_9456 0 16);
      v_9458 <- eval (extract v_9456 16 32);
      v_9459 <- eval (extract v_9456 32 48);
      v_9460 <- eval (extract v_9456 48 64);
      v_9461 <- eval (extract v_9456 64 80);
      v_9462 <- eval (extract v_9456 80 96);
      v_9463 <- eval (extract v_9456 96 112);
      v_9464 <- eval (extract v_9456 112 128);
      v_9465 <- eval (ult v_9463 v_9464);
      v_9466 <- eval (mux v_9465 v_9463 v_9464);
      v_9467 <- eval (ult v_9462 v_9466);
      v_9468 <- eval (mux v_9467 v_9462 v_9466);
      v_9469 <- eval (ult v_9461 v_9468);
      v_9470 <- eval (mux v_9469 v_9461 v_9468);
      v_9471 <- eval (ult v_9460 v_9470);
      v_9472 <- eval (mux v_9471 v_9460 v_9470);
      v_9473 <- eval (ult v_9459 v_9472);
      v_9474 <- eval (mux v_9473 v_9459 v_9472);
      v_9475 <- eval (ult v_9458 v_9474);
      v_9476 <- eval (mux v_9475 v_9458 v_9474);
      v_9477 <- eval (ult v_9457 v_9476);
      setRegister (lhs.of_reg v_3216) (concat (mux v_9477 (expression.bv_nat 112 7) (mux v_9475 (expression.bv_nat 112 6) (mux v_9473 (expression.bv_nat 112 5) (mux v_9471 (expression.bv_nat 112 4) (mux v_9469 (expression.bv_nat 112 3) (mux v_9467 (expression.bv_nat 112 2) (mux v_9465 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_9477 v_9457 v_9476));
      pure ()
    pat_end;
    pattern fun (v_3210 : Mem) (v_3211 : reg (bv 128)) => do
      v_18461 <- evaluateAddress v_3210;
      v_18462 <- load v_18461 16;
      v_18463 <- eval (extract v_18462 0 16);
      v_18464 <- eval (extract v_18462 16 32);
      v_18465 <- eval (extract v_18462 32 48);
      v_18466 <- eval (extract v_18462 48 64);
      v_18467 <- eval (extract v_18462 64 80);
      v_18468 <- eval (extract v_18462 80 96);
      v_18469 <- eval (extract v_18462 96 112);
      v_18470 <- eval (extract v_18462 112 128);
      v_18471 <- eval (ult v_18469 v_18470);
      v_18472 <- eval (mux v_18471 v_18469 v_18470);
      v_18473 <- eval (ult v_18468 v_18472);
      v_18474 <- eval (mux v_18473 v_18468 v_18472);
      v_18475 <- eval (ult v_18467 v_18474);
      v_18476 <- eval (mux v_18475 v_18467 v_18474);
      v_18477 <- eval (ult v_18466 v_18476);
      v_18478 <- eval (mux v_18477 v_18466 v_18476);
      v_18479 <- eval (ult v_18465 v_18478);
      v_18480 <- eval (mux v_18479 v_18465 v_18478);
      v_18481 <- eval (ult v_18464 v_18480);
      v_18482 <- eval (mux v_18481 v_18464 v_18480);
      v_18483 <- eval (ult v_18463 v_18482);
      setRegister (lhs.of_reg v_3211) (concat (mux v_18483 (expression.bv_nat 112 7) (mux v_18481 (expression.bv_nat 112 6) (mux v_18479 (expression.bv_nat 112 5) (mux v_18477 (expression.bv_nat 112 4) (mux v_18475 (expression.bv_nat 112 3) (mux v_18473 (expression.bv_nat 112 2) (mux v_18471 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_18483 v_18463 v_18482));
      pure ()
    pat_end
