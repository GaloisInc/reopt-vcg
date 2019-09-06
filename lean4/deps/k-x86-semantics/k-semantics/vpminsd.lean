def vpminsd1 : instruction :=
  definst "vpminsd" $ do
    pattern fun (v_2565 : reg (bv 128)) (v_2566 : reg (bv 128)) (v_2567 : reg (bv 128)) => do
      v_4714 <- getRegister v_2566;
      v_4715 <- eval (extract v_4714 0 32);
      v_4716 <- getRegister v_2565;
      v_4717 <- eval (extract v_4716 0 32);
      v_4720 <- eval (extract v_4714 32 64);
      v_4721 <- eval (extract v_4716 32 64);
      v_4724 <- eval (extract v_4714 64 96);
      v_4725 <- eval (extract v_4716 64 96);
      v_4728 <- eval (extract v_4714 96 128);
      v_4729 <- eval (extract v_4716 96 128);
      setRegister (lhs.of_reg v_2567) (concat (mux (slt v_4715 v_4717) v_4715 v_4717) (concat (mux (slt v_4720 v_4721) v_4720 v_4721) (concat (mux (slt v_4724 v_4725) v_4724 v_4725) (mux (slt v_4728 v_4729) v_4728 v_4729))));
      pure ()
    pat_end;
    pattern fun (v_2576 : reg (bv 256)) (v_2577 : reg (bv 256)) (v_2578 : reg (bv 256)) => do
      v_4741 <- getRegister v_2577;
      v_4742 <- eval (extract v_4741 0 32);
      v_4743 <- getRegister v_2576;
      v_4744 <- eval (extract v_4743 0 32);
      v_4747 <- eval (extract v_4741 32 64);
      v_4748 <- eval (extract v_4743 32 64);
      v_4751 <- eval (extract v_4741 64 96);
      v_4752 <- eval (extract v_4743 64 96);
      v_4755 <- eval (extract v_4741 96 128);
      v_4756 <- eval (extract v_4743 96 128);
      v_4759 <- eval (extract v_4741 128 160);
      v_4760 <- eval (extract v_4743 128 160);
      v_4763 <- eval (extract v_4741 160 192);
      v_4764 <- eval (extract v_4743 160 192);
      v_4767 <- eval (extract v_4741 192 224);
      v_4768 <- eval (extract v_4743 192 224);
      v_4771 <- eval (extract v_4741 224 256);
      v_4772 <- eval (extract v_4743 224 256);
      setRegister (lhs.of_reg v_2578) (concat (mux (slt v_4742 v_4744) v_4742 v_4744) (concat (mux (slt v_4747 v_4748) v_4747 v_4748) (concat (mux (slt v_4751 v_4752) v_4751 v_4752) (concat (mux (slt v_4755 v_4756) v_4755 v_4756) (concat (mux (slt v_4759 v_4760) v_4759 v_4760) (concat (mux (slt v_4763 v_4764) v_4763 v_4764) (concat (mux (slt v_4767 v_4768) v_4767 v_4768) (mux (slt v_4771 v_4772) v_4771 v_4772))))))));
      pure ()
    pat_end;
    pattern fun (v_2559 : Mem) (v_2560 : reg (bv 128)) (v_2561 : reg (bv 128)) => do
      v_11379 <- getRegister v_2560;
      v_11380 <- eval (extract v_11379 0 32);
      v_11381 <- evaluateAddress v_2559;
      v_11382 <- load v_11381 16;
      v_11383 <- eval (extract v_11382 0 32);
      v_11386 <- eval (extract v_11379 32 64);
      v_11387 <- eval (extract v_11382 32 64);
      v_11390 <- eval (extract v_11379 64 96);
      v_11391 <- eval (extract v_11382 64 96);
      v_11394 <- eval (extract v_11379 96 128);
      v_11395 <- eval (extract v_11382 96 128);
      setRegister (lhs.of_reg v_2561) (concat (mux (slt v_11380 v_11383) v_11380 v_11383) (concat (mux (slt v_11386 v_11387) v_11386 v_11387) (concat (mux (slt v_11390 v_11391) v_11390 v_11391) (mux (slt v_11394 v_11395) v_11394 v_11395))));
      pure ()
    pat_end;
    pattern fun (v_2570 : Mem) (v_2571 : reg (bv 256)) (v_2572 : reg (bv 256)) => do
      v_11402 <- getRegister v_2571;
      v_11403 <- eval (extract v_11402 0 32);
      v_11404 <- evaluateAddress v_2570;
      v_11405 <- load v_11404 32;
      v_11406 <- eval (extract v_11405 0 32);
      v_11409 <- eval (extract v_11402 32 64);
      v_11410 <- eval (extract v_11405 32 64);
      v_11413 <- eval (extract v_11402 64 96);
      v_11414 <- eval (extract v_11405 64 96);
      v_11417 <- eval (extract v_11402 96 128);
      v_11418 <- eval (extract v_11405 96 128);
      v_11421 <- eval (extract v_11402 128 160);
      v_11422 <- eval (extract v_11405 128 160);
      v_11425 <- eval (extract v_11402 160 192);
      v_11426 <- eval (extract v_11405 160 192);
      v_11429 <- eval (extract v_11402 192 224);
      v_11430 <- eval (extract v_11405 192 224);
      v_11433 <- eval (extract v_11402 224 256);
      v_11434 <- eval (extract v_11405 224 256);
      setRegister (lhs.of_reg v_2572) (concat (mux (slt v_11403 v_11406) v_11403 v_11406) (concat (mux (slt v_11409 v_11410) v_11409 v_11410) (concat (mux (slt v_11413 v_11414) v_11413 v_11414) (concat (mux (slt v_11417 v_11418) v_11417 v_11418) (concat (mux (slt v_11421 v_11422) v_11421 v_11422) (concat (mux (slt v_11425 v_11426) v_11425 v_11426) (concat (mux (slt v_11429 v_11430) v_11429 v_11430) (mux (slt v_11433 v_11434) v_11433 v_11434))))))));
      pure ()
    pat_end
