def vpminsd1 : instruction :=
  definst "vpminsd" $ do
    pattern fun (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) (v_2540 : reg (bv 128)) => do
      v_4687 <- getRegister v_2539;
      v_4688 <- eval (extract v_4687 0 32);
      v_4689 <- getRegister v_2538;
      v_4690 <- eval (extract v_4689 0 32);
      v_4693 <- eval (extract v_4687 32 64);
      v_4694 <- eval (extract v_4689 32 64);
      v_4697 <- eval (extract v_4687 64 96);
      v_4698 <- eval (extract v_4689 64 96);
      v_4701 <- eval (extract v_4687 96 128);
      v_4702 <- eval (extract v_4689 96 128);
      setRegister (lhs.of_reg v_2540) (concat (mux (slt v_4688 v_4690) v_4688 v_4690) (concat (mux (slt v_4693 v_4694) v_4693 v_4694) (concat (mux (slt v_4697 v_4698) v_4697 v_4698) (mux (slt v_4701 v_4702) v_4701 v_4702))));
      pure ()
    pat_end;
    pattern fun (v_2549 : reg (bv 256)) (v_2550 : reg (bv 256)) (v_2551 : reg (bv 256)) => do
      v_4714 <- getRegister v_2550;
      v_4715 <- eval (extract v_4714 0 32);
      v_4716 <- getRegister v_2549;
      v_4717 <- eval (extract v_4716 0 32);
      v_4720 <- eval (extract v_4714 32 64);
      v_4721 <- eval (extract v_4716 32 64);
      v_4724 <- eval (extract v_4714 64 96);
      v_4725 <- eval (extract v_4716 64 96);
      v_4728 <- eval (extract v_4714 96 128);
      v_4729 <- eval (extract v_4716 96 128);
      v_4732 <- eval (extract v_4714 128 160);
      v_4733 <- eval (extract v_4716 128 160);
      v_4736 <- eval (extract v_4714 160 192);
      v_4737 <- eval (extract v_4716 160 192);
      v_4740 <- eval (extract v_4714 192 224);
      v_4741 <- eval (extract v_4716 192 224);
      v_4744 <- eval (extract v_4714 224 256);
      v_4745 <- eval (extract v_4716 224 256);
      setRegister (lhs.of_reg v_2551) (concat (mux (slt v_4715 v_4717) v_4715 v_4717) (concat (mux (slt v_4720 v_4721) v_4720 v_4721) (concat (mux (slt v_4724 v_4725) v_4724 v_4725) (concat (mux (slt v_4728 v_4729) v_4728 v_4729) (concat (mux (slt v_4732 v_4733) v_4732 v_4733) (concat (mux (slt v_4736 v_4737) v_4736 v_4737) (concat (mux (slt v_4740 v_4741) v_4740 v_4741) (mux (slt v_4744 v_4745) v_4744 v_4745))))))));
      pure ()
    pat_end;
    pattern fun (v_2532 : Mem) (v_2533 : reg (bv 128)) (v_2534 : reg (bv 128)) => do
      v_11352 <- getRegister v_2533;
      v_11353 <- eval (extract v_11352 0 32);
      v_11354 <- evaluateAddress v_2532;
      v_11355 <- load v_11354 16;
      v_11356 <- eval (extract v_11355 0 32);
      v_11359 <- eval (extract v_11352 32 64);
      v_11360 <- eval (extract v_11355 32 64);
      v_11363 <- eval (extract v_11352 64 96);
      v_11364 <- eval (extract v_11355 64 96);
      v_11367 <- eval (extract v_11352 96 128);
      v_11368 <- eval (extract v_11355 96 128);
      setRegister (lhs.of_reg v_2534) (concat (mux (slt v_11353 v_11356) v_11353 v_11356) (concat (mux (slt v_11359 v_11360) v_11359 v_11360) (concat (mux (slt v_11363 v_11364) v_11363 v_11364) (mux (slt v_11367 v_11368) v_11367 v_11368))));
      pure ()
    pat_end;
    pattern fun (v_2543 : Mem) (v_2544 : reg (bv 256)) (v_2545 : reg (bv 256)) => do
      v_11375 <- getRegister v_2544;
      v_11376 <- eval (extract v_11375 0 32);
      v_11377 <- evaluateAddress v_2543;
      v_11378 <- load v_11377 32;
      v_11379 <- eval (extract v_11378 0 32);
      v_11382 <- eval (extract v_11375 32 64);
      v_11383 <- eval (extract v_11378 32 64);
      v_11386 <- eval (extract v_11375 64 96);
      v_11387 <- eval (extract v_11378 64 96);
      v_11390 <- eval (extract v_11375 96 128);
      v_11391 <- eval (extract v_11378 96 128);
      v_11394 <- eval (extract v_11375 128 160);
      v_11395 <- eval (extract v_11378 128 160);
      v_11398 <- eval (extract v_11375 160 192);
      v_11399 <- eval (extract v_11378 160 192);
      v_11402 <- eval (extract v_11375 192 224);
      v_11403 <- eval (extract v_11378 192 224);
      v_11406 <- eval (extract v_11375 224 256);
      v_11407 <- eval (extract v_11378 224 256);
      setRegister (lhs.of_reg v_2545) (concat (mux (slt v_11376 v_11379) v_11376 v_11379) (concat (mux (slt v_11382 v_11383) v_11382 v_11383) (concat (mux (slt v_11386 v_11387) v_11386 v_11387) (concat (mux (slt v_11390 v_11391) v_11390 v_11391) (concat (mux (slt v_11394 v_11395) v_11394 v_11395) (concat (mux (slt v_11398 v_11399) v_11398 v_11399) (concat (mux (slt v_11402 v_11403) v_11402 v_11403) (mux (slt v_11406 v_11407) v_11406 v_11407))))))));
      pure ()
    pat_end
