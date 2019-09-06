def vphsubsw1 : instruction :=
  definst "vphsubsw" $ do
    pattern fun (v_3337 : reg (bv 128)) (v_3338 : reg (bv 128)) (v_3339 : reg (bv 128)) => do
      v_9238 <- getRegister v_3337;
      v_9243 <- eval (sub (sext (extract v_9238 16 32) 32) (sext (extract v_9238 0 16) 32));
      v_9253 <- eval (sub (sext (extract v_9238 48 64) 32) (sext (extract v_9238 32 48) 32));
      v_9263 <- eval (sub (sext (extract v_9238 80 96) 32) (sext (extract v_9238 64 80) 32));
      v_9273 <- eval (sub (sext (extract v_9238 112 128) 32) (sext (extract v_9238 96 112) 32));
      v_9279 <- getRegister v_3338;
      v_9284 <- eval (sub (sext (extract v_9279 16 32) 32) (sext (extract v_9279 0 16) 32));
      v_9294 <- eval (sub (sext (extract v_9279 48 64) 32) (sext (extract v_9279 32 48) 32));
      v_9304 <- eval (sub (sext (extract v_9279 80 96) 32) (sext (extract v_9279 64 80) 32));
      v_9314 <- eval (sub (sext (extract v_9279 112 128) 32) (sext (extract v_9279 96 112) 32));
      setRegister (lhs.of_reg v_3339) (concat (mux (sgt v_9243 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9243 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9243 16 32))) (concat (mux (sgt v_9253 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9253 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9253 16 32))) (concat (mux (sgt v_9263 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9263 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9263 16 32))) (concat (mux (sgt v_9273 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9273 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9273 16 32))) (concat (mux (sgt v_9284 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9284 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9284 16 32))) (concat (mux (sgt v_9294 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9294 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9294 16 32))) (concat (mux (sgt v_9304 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9304 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9304 16 32))) (mux (sgt v_9314 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9314 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9314 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3348 : reg (bv 256)) (v_3349 : reg (bv 256)) (v_3350 : reg (bv 256)) => do
      v_9333 <- getRegister v_3348;
      v_9338 <- eval (sub (sext (extract v_9333 16 32) 32) (sext (extract v_9333 0 16) 32));
      v_9348 <- eval (sub (sext (extract v_9333 48 64) 32) (sext (extract v_9333 32 48) 32));
      v_9358 <- eval (sub (sext (extract v_9333 80 96) 32) (sext (extract v_9333 64 80) 32));
      v_9368 <- eval (sub (sext (extract v_9333 112 128) 32) (sext (extract v_9333 96 112) 32));
      v_9374 <- getRegister v_3349;
      v_9379 <- eval (sub (sext (extract v_9374 16 32) 32) (sext (extract v_9374 0 16) 32));
      v_9389 <- eval (sub (sext (extract v_9374 48 64) 32) (sext (extract v_9374 32 48) 32));
      v_9399 <- eval (sub (sext (extract v_9374 80 96) 32) (sext (extract v_9374 64 80) 32));
      v_9409 <- eval (sub (sext (extract v_9374 112 128) 32) (sext (extract v_9374 96 112) 32));
      v_9419 <- eval (sub (sext (extract v_9333 144 160) 32) (sext (extract v_9333 128 144) 32));
      v_9429 <- eval (sub (sext (extract v_9333 176 192) 32) (sext (extract v_9333 160 176) 32));
      v_9439 <- eval (sub (sext (extract v_9333 208 224) 32) (sext (extract v_9333 192 208) 32));
      v_9449 <- eval (sub (sext (extract v_9333 240 256) 32) (sext (extract v_9333 224 240) 32));
      v_9459 <- eval (sub (sext (extract v_9374 144 160) 32) (sext (extract v_9374 128 144) 32));
      v_9469 <- eval (sub (sext (extract v_9374 176 192) 32) (sext (extract v_9374 160 176) 32));
      v_9479 <- eval (sub (sext (extract v_9374 208 224) 32) (sext (extract v_9374 192 208) 32));
      v_9489 <- eval (sub (sext (extract v_9374 240 256) 32) (sext (extract v_9374 224 240) 32));
      setRegister (lhs.of_reg v_3350) (concat (mux (sgt v_9338 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9338 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9338 16 32))) (concat (mux (sgt v_9348 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9348 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9348 16 32))) (concat (mux (sgt v_9358 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9358 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9358 16 32))) (concat (mux (sgt v_9368 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9368 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9368 16 32))) (concat (mux (sgt v_9379 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9379 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9379 16 32))) (concat (mux (sgt v_9389 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9389 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9389 16 32))) (concat (mux (sgt v_9399 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9399 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9399 16 32))) (concat (mux (sgt v_9409 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9409 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9409 16 32))) (concat (mux (sgt v_9419 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9419 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9419 16 32))) (concat (mux (sgt v_9429 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9429 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9429 16 32))) (concat (mux (sgt v_9439 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9439 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9439 16 32))) (concat (mux (sgt v_9449 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9449 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9449 16 32))) (concat (mux (sgt v_9459 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9459 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9459 16 32))) (concat (mux (sgt v_9469 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9469 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9469 16 32))) (concat (mux (sgt v_9479 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9479 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9479 16 32))) (mux (sgt v_9489 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9489 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9489 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3332 : Mem) (v_3333 : reg (bv 128)) (v_3334 : reg (bv 128)) => do
      v_17623 <- evaluateAddress v_3332;
      v_17624 <- load v_17623 16;
      v_17629 <- eval (sub (sext (extract v_17624 16 32) 32) (sext (extract v_17624 0 16) 32));
      v_17639 <- eval (sub (sext (extract v_17624 48 64) 32) (sext (extract v_17624 32 48) 32));
      v_17649 <- eval (sub (sext (extract v_17624 80 96) 32) (sext (extract v_17624 64 80) 32));
      v_17659 <- eval (sub (sext (extract v_17624 112 128) 32) (sext (extract v_17624 96 112) 32));
      v_17665 <- getRegister v_3333;
      v_17670 <- eval (sub (sext (extract v_17665 16 32) 32) (sext (extract v_17665 0 16) 32));
      v_17680 <- eval (sub (sext (extract v_17665 48 64) 32) (sext (extract v_17665 32 48) 32));
      v_17690 <- eval (sub (sext (extract v_17665 80 96) 32) (sext (extract v_17665 64 80) 32));
      v_17700 <- eval (sub (sext (extract v_17665 112 128) 32) (sext (extract v_17665 96 112) 32));
      setRegister (lhs.of_reg v_3334) (concat (mux (sgt v_17629 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17629 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17629 16 32))) (concat (mux (sgt v_17639 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17639 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17639 16 32))) (concat (mux (sgt v_17649 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17649 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17649 16 32))) (concat (mux (sgt v_17659 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17659 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17659 16 32))) (concat (mux (sgt v_17670 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17670 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17670 16 32))) (concat (mux (sgt v_17680 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17680 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17680 16 32))) (concat (mux (sgt v_17690 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17690 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17690 16 32))) (mux (sgt v_17700 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17700 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17700 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3343 : Mem) (v_3344 : reg (bv 256)) (v_3345 : reg (bv 256)) => do
      v_17714 <- evaluateAddress v_3343;
      v_17715 <- load v_17714 32;
      v_17720 <- eval (sub (sext (extract v_17715 16 32) 32) (sext (extract v_17715 0 16) 32));
      v_17730 <- eval (sub (sext (extract v_17715 48 64) 32) (sext (extract v_17715 32 48) 32));
      v_17740 <- eval (sub (sext (extract v_17715 80 96) 32) (sext (extract v_17715 64 80) 32));
      v_17750 <- eval (sub (sext (extract v_17715 112 128) 32) (sext (extract v_17715 96 112) 32));
      v_17756 <- getRegister v_3344;
      v_17761 <- eval (sub (sext (extract v_17756 16 32) 32) (sext (extract v_17756 0 16) 32));
      v_17771 <- eval (sub (sext (extract v_17756 48 64) 32) (sext (extract v_17756 32 48) 32));
      v_17781 <- eval (sub (sext (extract v_17756 80 96) 32) (sext (extract v_17756 64 80) 32));
      v_17791 <- eval (sub (sext (extract v_17756 112 128) 32) (sext (extract v_17756 96 112) 32));
      v_17801 <- eval (sub (sext (extract v_17715 144 160) 32) (sext (extract v_17715 128 144) 32));
      v_17811 <- eval (sub (sext (extract v_17715 176 192) 32) (sext (extract v_17715 160 176) 32));
      v_17821 <- eval (sub (sext (extract v_17715 208 224) 32) (sext (extract v_17715 192 208) 32));
      v_17831 <- eval (sub (sext (extract v_17715 240 256) 32) (sext (extract v_17715 224 240) 32));
      v_17841 <- eval (sub (sext (extract v_17756 144 160) 32) (sext (extract v_17756 128 144) 32));
      v_17851 <- eval (sub (sext (extract v_17756 176 192) 32) (sext (extract v_17756 160 176) 32));
      v_17861 <- eval (sub (sext (extract v_17756 208 224) 32) (sext (extract v_17756 192 208) 32));
      v_17871 <- eval (sub (sext (extract v_17756 240 256) 32) (sext (extract v_17756 224 240) 32));
      setRegister (lhs.of_reg v_3345) (concat (mux (sgt v_17720 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17720 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17720 16 32))) (concat (mux (sgt v_17730 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17730 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17730 16 32))) (concat (mux (sgt v_17740 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17740 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17740 16 32))) (concat (mux (sgt v_17750 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17750 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17750 16 32))) (concat (mux (sgt v_17761 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17761 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17761 16 32))) (concat (mux (sgt v_17771 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17771 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17771 16 32))) (concat (mux (sgt v_17781 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17781 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17781 16 32))) (concat (mux (sgt v_17791 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17791 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17791 16 32))) (concat (mux (sgt v_17801 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17801 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17801 16 32))) (concat (mux (sgt v_17811 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17811 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17811 16 32))) (concat (mux (sgt v_17821 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17821 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17821 16 32))) (concat (mux (sgt v_17831 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17831 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17831 16 32))) (concat (mux (sgt v_17841 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17841 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17841 16 32))) (concat (mux (sgt v_17851 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17851 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17851 16 32))) (concat (mux (sgt v_17861 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17861 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17861 16 32))) (mux (sgt v_17871 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17871 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17871 16 32))))))))))))))))));
      pure ()
    pat_end
