def packsswb1 : instruction :=
  definst "packsswb" $ do
    pattern fun (v_3096 : reg (bv 128)) (v_3097 : reg (bv 128)) => do
      v_5407 <- getRegister v_3096;
      v_5408 <- eval (extract v_5407 0 16);
      v_5414 <- eval (extract v_5407 16 32);
      v_5420 <- eval (extract v_5407 32 48);
      v_5426 <- eval (extract v_5407 48 64);
      v_5432 <- eval (extract v_5407 64 80);
      v_5438 <- eval (extract v_5407 80 96);
      v_5444 <- eval (extract v_5407 96 112);
      v_5450 <- eval (extract v_5407 112 128);
      v_5456 <- getRegister v_3097;
      v_5457 <- eval (extract v_5456 0 16);
      v_5463 <- eval (extract v_5456 16 32);
      v_5469 <- eval (extract v_5456 32 48);
      v_5475 <- eval (extract v_5456 48 64);
      v_5481 <- eval (extract v_5456 64 80);
      v_5487 <- eval (extract v_5456 80 96);
      v_5493 <- eval (extract v_5456 96 112);
      v_5499 <- eval (extract v_5456 112 128);
      setRegister (lhs.of_reg v_3097) (concat (mux (sgt v_5408 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5408 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 8 16))) (concat (mux (sgt v_5414 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5414 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 24 32))) (concat (mux (sgt v_5420 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5420 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 40 48))) (concat (mux (sgt v_5426 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5426 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 56 64))) (concat (mux (sgt v_5432 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5432 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 72 80))) (concat (mux (sgt v_5438 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5438 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 88 96))) (concat (mux (sgt v_5444 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5444 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 104 112))) (concat (mux (sgt v_5450 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5450 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5407 120 128))) (concat (mux (sgt v_5457 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5457 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 8 16))) (concat (mux (sgt v_5463 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5463 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 24 32))) (concat (mux (sgt v_5469 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5469 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 40 48))) (concat (mux (sgt v_5475 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5475 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 56 64))) (concat (mux (sgt v_5481 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5481 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 72 80))) (concat (mux (sgt v_5487 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5487 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 88 96))) (concat (mux (sgt v_5493 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5493 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 104 112))) (mux (sgt v_5499 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5499 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5456 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3092 : Mem) (v_3093 : reg (bv 128)) => do
      v_9500 <- evaluateAddress v_3092;
      v_9501 <- load v_9500 16;
      v_9502 <- eval (extract v_9501 0 16);
      v_9508 <- eval (extract v_9501 16 32);
      v_9514 <- eval (extract v_9501 32 48);
      v_9520 <- eval (extract v_9501 48 64);
      v_9526 <- eval (extract v_9501 64 80);
      v_9532 <- eval (extract v_9501 80 96);
      v_9538 <- eval (extract v_9501 96 112);
      v_9544 <- eval (extract v_9501 112 128);
      v_9550 <- getRegister v_3093;
      v_9551 <- eval (extract v_9550 0 16);
      v_9557 <- eval (extract v_9550 16 32);
      v_9563 <- eval (extract v_9550 32 48);
      v_9569 <- eval (extract v_9550 48 64);
      v_9575 <- eval (extract v_9550 64 80);
      v_9581 <- eval (extract v_9550 80 96);
      v_9587 <- eval (extract v_9550 96 112);
      v_9593 <- eval (extract v_9550 112 128);
      setRegister (lhs.of_reg v_3093) (concat (mux (sgt v_9502 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9502 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 8 16))) (concat (mux (sgt v_9508 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9508 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 24 32))) (concat (mux (sgt v_9514 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9514 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 40 48))) (concat (mux (sgt v_9520 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9520 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 56 64))) (concat (mux (sgt v_9526 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9526 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 72 80))) (concat (mux (sgt v_9532 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9532 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 88 96))) (concat (mux (sgt v_9538 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9538 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 104 112))) (concat (mux (sgt v_9544 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9544 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9501 120 128))) (concat (mux (sgt v_9551 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9551 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 8 16))) (concat (mux (sgt v_9557 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9557 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 24 32))) (concat (mux (sgt v_9563 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9563 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 40 48))) (concat (mux (sgt v_9569 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9569 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 56 64))) (concat (mux (sgt v_9575 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9575 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 72 80))) (concat (mux (sgt v_9581 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9581 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 88 96))) (concat (mux (sgt v_9587 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9587 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 104 112))) (mux (sgt v_9593 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9593 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9550 120 128))))))))))))))))));
      pure ()
    pat_end
