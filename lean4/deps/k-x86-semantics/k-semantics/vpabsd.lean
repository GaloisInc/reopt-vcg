def vpabsd1 : instruction :=
  definst "vpabsd" $ do
    pattern fun (v_3260 : reg (bv 128)) (v_3261 : reg (bv 128)) => do
      v_5673 <- getRegister v_3260;
      v_5674 <- eval (extract v_5673 0 32);
      v_5679 <- eval (extract v_5673 32 64);
      v_5684 <- eval (extract v_5673 64 96);
      v_5689 <- eval (extract v_5673 96 128);
      setRegister (lhs.of_reg v_3261) (concat (mux (ugt v_5674 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5674 (expression.bv_nat 32 4294967295))) v_5674) (concat (mux (ugt v_5679 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5679 (expression.bv_nat 32 4294967295))) v_5679) (concat (mux (ugt v_5684 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5684 (expression.bv_nat 32 4294967295))) v_5684) (mux (ugt v_5689 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5689 (expression.bv_nat 32 4294967295))) v_5689))));
      pure ()
    pat_end;
    pattern fun (v_3270 : reg (bv 256)) (v_3271 : reg (bv 256)) => do
      v_5702 <- getRegister v_3270;
      v_5703 <- eval (extract v_5702 0 32);
      v_5708 <- eval (extract v_5702 32 64);
      v_5713 <- eval (extract v_5702 64 96);
      v_5718 <- eval (extract v_5702 96 128);
      v_5723 <- eval (extract v_5702 128 160);
      v_5728 <- eval (extract v_5702 160 192);
      v_5733 <- eval (extract v_5702 192 224);
      v_5738 <- eval (extract v_5702 224 256);
      setRegister (lhs.of_reg v_3271) (concat (mux (ugt v_5703 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5703 (expression.bv_nat 32 4294967295))) v_5703) (concat (mux (ugt v_5708 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5708 (expression.bv_nat 32 4294967295))) v_5708) (concat (mux (ugt v_5713 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5713 (expression.bv_nat 32 4294967295))) v_5713) (concat (mux (ugt v_5718 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5718 (expression.bv_nat 32 4294967295))) v_5718) (concat (mux (ugt v_5723 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5723 (expression.bv_nat 32 4294967295))) v_5723) (concat (mux (ugt v_5728 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5728 (expression.bv_nat 32 4294967295))) v_5728) (concat (mux (ugt v_5733 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5733 (expression.bv_nat 32 4294967295))) v_5733) (mux (ugt v_5738 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5738 (expression.bv_nat 32 4294967295))) v_5738))))))));
      pure ()
    pat_end;
    pattern fun (v_3256 : Mem) (v_3257 : reg (bv 128)) => do
      v_10758 <- evaluateAddress v_3256;
      v_10759 <- load v_10758 16;
      v_10760 <- eval (extract v_10759 0 32);
      v_10765 <- eval (extract v_10759 32 64);
      v_10770 <- eval (extract v_10759 64 96);
      v_10775 <- eval (extract v_10759 96 128);
      setRegister (lhs.of_reg v_3257) (concat (mux (ugt v_10760 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10760 (expression.bv_nat 32 4294967295))) v_10760) (concat (mux (ugt v_10765 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10765 (expression.bv_nat 32 4294967295))) v_10765) (concat (mux (ugt v_10770 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10770 (expression.bv_nat 32 4294967295))) v_10770) (mux (ugt v_10775 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10775 (expression.bv_nat 32 4294967295))) v_10775))));
      pure ()
    pat_end;
    pattern fun (v_3265 : Mem) (v_3266 : reg (bv 256)) => do
      v_10784 <- evaluateAddress v_3265;
      v_10785 <- load v_10784 32;
      v_10786 <- eval (extract v_10785 0 32);
      v_10791 <- eval (extract v_10785 32 64);
      v_10796 <- eval (extract v_10785 64 96);
      v_10801 <- eval (extract v_10785 96 128);
      v_10806 <- eval (extract v_10785 128 160);
      v_10811 <- eval (extract v_10785 160 192);
      v_10816 <- eval (extract v_10785 192 224);
      v_10821 <- eval (extract v_10785 224 256);
      setRegister (lhs.of_reg v_3266) (concat (mux (ugt v_10786 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10786 (expression.bv_nat 32 4294967295))) v_10786) (concat (mux (ugt v_10791 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10791 (expression.bv_nat 32 4294967295))) v_10791) (concat (mux (ugt v_10796 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10796 (expression.bv_nat 32 4294967295))) v_10796) (concat (mux (ugt v_10801 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10801 (expression.bv_nat 32 4294967295))) v_10801) (concat (mux (ugt v_10806 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10806 (expression.bv_nat 32 4294967295))) v_10806) (concat (mux (ugt v_10811 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10811 (expression.bv_nat 32 4294967295))) v_10811) (concat (mux (ugt v_10816 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10816 (expression.bv_nat 32 4294967295))) v_10816) (mux (ugt v_10821 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10821 (expression.bv_nat 32 4294967295))) v_10821))))))));
      pure ()
    pat_end
