def phsubw1 : instruction :=
  definst "phsubw" $ do
    pattern fun (v_2545 : reg (bv 128)) (v_2546 : reg (bv 128)) => do
      v_4399 <- getRegister v_2545;
      v_4415 <- getRegister v_2546;
      setRegister (lhs.of_reg v_2546) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_4399 16 32) (extract v_4399 0 16)) (sub (extract v_4399 48 64) (extract v_4399 32 48))) (sub (extract v_4399 80 96) (extract v_4399 64 80))) (sub (extract v_4399 112 128) (extract v_4399 96 112))) (sub (extract v_4415 16 32) (extract v_4415 0 16))) (sub (extract v_4415 48 64) (extract v_4415 32 48))) (sub (extract v_4415 80 96) (extract v_4415 64 80))) (sub (extract v_4415 112 128) (extract v_4415 96 112)));
      pure ()
    pat_end;
    pattern fun (v_2542 : Mem) (v_2541 : reg (bv 128)) => do
      v_11341 <- evaluateAddress v_2542;
      v_11342 <- load v_11341 16;
      v_11358 <- getRegister v_2541;
      setRegister (lhs.of_reg v_2541) (concat (concat (concat (concat (concat (concat (concat (sub (extract v_11342 16 32) (extract v_11342 0 16)) (sub (extract v_11342 48 64) (extract v_11342 32 48))) (sub (extract v_11342 80 96) (extract v_11342 64 80))) (sub (extract v_11342 112 128) (extract v_11342 96 112))) (sub (extract v_11358 16 32) (extract v_11358 0 16))) (sub (extract v_11358 48 64) (extract v_11358 32 48))) (sub (extract v_11358 80 96) (extract v_11358 64 80))) (sub (extract v_11358 112 128) (extract v_11358 96 112)));
      pure ()
    pat_end
