def vpabsd1 : instruction :=
  definst "vpabsd" $ do
    pattern fun (v_3285 : reg (bv 128)) (v_3286 : reg (bv 128)) => do
      v_5700 <- getRegister v_3285;
      v_5701 <- eval (extract v_5700 0 32);
      v_5706 <- eval (extract v_5700 32 64);
      v_5711 <- eval (extract v_5700 64 96);
      v_5716 <- eval (extract v_5700 96 128);
      setRegister (lhs.of_reg v_3286) (concat (mux (ugt v_5701 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5701 (expression.bv_nat 32 4294967295))) v_5701) (concat (mux (ugt v_5706 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5706 (expression.bv_nat 32 4294967295))) v_5706) (concat (mux (ugt v_5711 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5711 (expression.bv_nat 32 4294967295))) v_5711) (mux (ugt v_5716 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5716 (expression.bv_nat 32 4294967295))) v_5716))));
      pure ()
    pat_end;
    pattern fun (v_3294 : reg (bv 256)) (v_3295 : reg (bv 256)) => do
      v_5729 <- getRegister v_3294;
      v_5730 <- eval (extract v_5729 0 32);
      v_5735 <- eval (extract v_5729 32 64);
      v_5740 <- eval (extract v_5729 64 96);
      v_5745 <- eval (extract v_5729 96 128);
      v_5750 <- eval (extract v_5729 128 160);
      v_5755 <- eval (extract v_5729 160 192);
      v_5760 <- eval (extract v_5729 192 224);
      v_5765 <- eval (extract v_5729 224 256);
      setRegister (lhs.of_reg v_3295) (concat (mux (ugt v_5730 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5730 (expression.bv_nat 32 4294967295))) v_5730) (concat (mux (ugt v_5735 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5735 (expression.bv_nat 32 4294967295))) v_5735) (concat (mux (ugt v_5740 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5740 (expression.bv_nat 32 4294967295))) v_5740) (concat (mux (ugt v_5745 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5745 (expression.bv_nat 32 4294967295))) v_5745) (concat (mux (ugt v_5750 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5750 (expression.bv_nat 32 4294967295))) v_5750) (concat (mux (ugt v_5755 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5755 (expression.bv_nat 32 4294967295))) v_5755) (concat (mux (ugt v_5760 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5760 (expression.bv_nat 32 4294967295))) v_5760) (mux (ugt v_5765 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_5765 (expression.bv_nat 32 4294967295))) v_5765))))))));
      pure ()
    pat_end;
    pattern fun (v_3281 : Mem) (v_3282 : reg (bv 128)) => do
      v_10785 <- evaluateAddress v_3281;
      v_10786 <- load v_10785 16;
      v_10787 <- eval (extract v_10786 0 32);
      v_10792 <- eval (extract v_10786 32 64);
      v_10797 <- eval (extract v_10786 64 96);
      v_10802 <- eval (extract v_10786 96 128);
      setRegister (lhs.of_reg v_3282) (concat (mux (ugt v_10787 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10787 (expression.bv_nat 32 4294967295))) v_10787) (concat (mux (ugt v_10792 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10792 (expression.bv_nat 32 4294967295))) v_10792) (concat (mux (ugt v_10797 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10797 (expression.bv_nat 32 4294967295))) v_10797) (mux (ugt v_10802 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10802 (expression.bv_nat 32 4294967295))) v_10802))));
      pure ()
    pat_end;
    pattern fun (v_3290 : Mem) (v_3291 : reg (bv 256)) => do
      v_10811 <- evaluateAddress v_3290;
      v_10812 <- load v_10811 32;
      v_10813 <- eval (extract v_10812 0 32);
      v_10818 <- eval (extract v_10812 32 64);
      v_10823 <- eval (extract v_10812 64 96);
      v_10828 <- eval (extract v_10812 96 128);
      v_10833 <- eval (extract v_10812 128 160);
      v_10838 <- eval (extract v_10812 160 192);
      v_10843 <- eval (extract v_10812 192 224);
      v_10848 <- eval (extract v_10812 224 256);
      setRegister (lhs.of_reg v_3291) (concat (mux (ugt v_10813 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10813 (expression.bv_nat 32 4294967295))) v_10813) (concat (mux (ugt v_10818 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10818 (expression.bv_nat 32 4294967295))) v_10818) (concat (mux (ugt v_10823 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10823 (expression.bv_nat 32 4294967295))) v_10823) (concat (mux (ugt v_10828 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10828 (expression.bv_nat 32 4294967295))) v_10828) (concat (mux (ugt v_10833 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10833 (expression.bv_nat 32 4294967295))) v_10833) (concat (mux (ugt v_10838 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10838 (expression.bv_nat 32 4294967295))) v_10838) (concat (mux (ugt v_10843 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10843 (expression.bv_nat 32 4294967295))) v_10843) (mux (ugt v_10848 (expression.bv_nat 32 2147483647)) (add (expression.bv_nat 32 1) (bv_xor v_10848 (expression.bv_nat 32 4294967295))) v_10848))))))));
      pure ()
    pat_end
