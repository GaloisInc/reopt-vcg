def vpminsd1 : instruction :=
  definst "vpminsd" $ do
    pattern fun (v_2485 : reg (bv 128)) (v_2486 : reg (bv 128)) (v_2487 : reg (bv 128)) => do
      v_4636 <- getRegister v_2486;
      v_4637 <- eval (extract v_4636 0 32);
      v_4638 <- getRegister v_2485;
      v_4639 <- eval (extract v_4638 0 32);
      v_4642 <- eval (extract v_4636 32 64);
      v_4643 <- eval (extract v_4638 32 64);
      v_4646 <- eval (extract v_4636 64 96);
      v_4647 <- eval (extract v_4638 64 96);
      v_4650 <- eval (extract v_4636 96 128);
      v_4651 <- eval (extract v_4638 96 128);
      setRegister (lhs.of_reg v_2487) (concat (mux (slt v_4637 v_4639) v_4637 v_4639) (concat (mux (slt v_4642 v_4643) v_4642 v_4643) (concat (mux (slt v_4646 v_4647) v_4646 v_4647) (mux (slt v_4650 v_4651) v_4650 v_4651))));
      pure ()
    pat_end;
    pattern fun (v_2497 : reg (bv 256)) (v_2498 : reg (bv 256)) (v_2499 : reg (bv 256)) => do
      v_4663 <- getRegister v_2498;
      v_4664 <- eval (extract v_4663 0 32);
      v_4665 <- getRegister v_2497;
      v_4666 <- eval (extract v_4665 0 32);
      v_4669 <- eval (extract v_4663 32 64);
      v_4670 <- eval (extract v_4665 32 64);
      v_4673 <- eval (extract v_4663 64 96);
      v_4674 <- eval (extract v_4665 64 96);
      v_4677 <- eval (extract v_4663 96 128);
      v_4678 <- eval (extract v_4665 96 128);
      v_4681 <- eval (extract v_4663 128 160);
      v_4682 <- eval (extract v_4665 128 160);
      v_4685 <- eval (extract v_4663 160 192);
      v_4686 <- eval (extract v_4665 160 192);
      v_4689 <- eval (extract v_4663 192 224);
      v_4690 <- eval (extract v_4665 192 224);
      v_4693 <- eval (extract v_4663 224 256);
      v_4694 <- eval (extract v_4665 224 256);
      setRegister (lhs.of_reg v_2499) (concat (mux (slt v_4664 v_4666) v_4664 v_4666) (concat (mux (slt v_4669 v_4670) v_4669 v_4670) (concat (mux (slt v_4673 v_4674) v_4673 v_4674) (concat (mux (slt v_4677 v_4678) v_4677 v_4678) (concat (mux (slt v_4681 v_4682) v_4681 v_4682) (concat (mux (slt v_4685 v_4686) v_4685 v_4686) (concat (mux (slt v_4689 v_4690) v_4689 v_4690) (mux (slt v_4693 v_4694) v_4693 v_4694))))))));
      pure ()
    pat_end;
    pattern fun (v_2479 : Mem) (v_2480 : reg (bv 128)) (v_2481 : reg (bv 128)) => do
      v_11557 <- getRegister v_2480;
      v_11558 <- eval (extract v_11557 0 32);
      v_11559 <- evaluateAddress v_2479;
      v_11560 <- load v_11559 16;
      v_11561 <- eval (extract v_11560 0 32);
      v_11564 <- eval (extract v_11557 32 64);
      v_11565 <- eval (extract v_11560 32 64);
      v_11568 <- eval (extract v_11557 64 96);
      v_11569 <- eval (extract v_11560 64 96);
      v_11572 <- eval (extract v_11557 96 128);
      v_11573 <- eval (extract v_11560 96 128);
      setRegister (lhs.of_reg v_2481) (concat (mux (slt v_11558 v_11561) v_11558 v_11561) (concat (mux (slt v_11564 v_11565) v_11564 v_11565) (concat (mux (slt v_11568 v_11569) v_11568 v_11569) (mux (slt v_11572 v_11573) v_11572 v_11573))));
      pure ()
    pat_end;
    pattern fun (v_2490 : Mem) (v_2492 : reg (bv 256)) (v_2493 : reg (bv 256)) => do
      v_11580 <- getRegister v_2492;
      v_11581 <- eval (extract v_11580 0 32);
      v_11582 <- evaluateAddress v_2490;
      v_11583 <- load v_11582 32;
      v_11584 <- eval (extract v_11583 0 32);
      v_11587 <- eval (extract v_11580 32 64);
      v_11588 <- eval (extract v_11583 32 64);
      v_11591 <- eval (extract v_11580 64 96);
      v_11592 <- eval (extract v_11583 64 96);
      v_11595 <- eval (extract v_11580 96 128);
      v_11596 <- eval (extract v_11583 96 128);
      v_11599 <- eval (extract v_11580 128 160);
      v_11600 <- eval (extract v_11583 128 160);
      v_11603 <- eval (extract v_11580 160 192);
      v_11604 <- eval (extract v_11583 160 192);
      v_11607 <- eval (extract v_11580 192 224);
      v_11608 <- eval (extract v_11583 192 224);
      v_11611 <- eval (extract v_11580 224 256);
      v_11612 <- eval (extract v_11583 224 256);
      setRegister (lhs.of_reg v_2493) (concat (mux (slt v_11581 v_11584) v_11581 v_11584) (concat (mux (slt v_11587 v_11588) v_11587 v_11588) (concat (mux (slt v_11591 v_11592) v_11591 v_11592) (concat (mux (slt v_11595 v_11596) v_11595 v_11596) (concat (mux (slt v_11599 v_11600) v_11599 v_11600) (concat (mux (slt v_11603 v_11604) v_11603 v_11604) (concat (mux (slt v_11607 v_11608) v_11607 v_11608) (mux (slt v_11611 v_11612) v_11611 v_11612))))))));
      pure ()
    pat_end
