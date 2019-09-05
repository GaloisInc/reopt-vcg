def vpabsw1 : instruction :=
  definst "vpabsw" $ do
    pattern fun (v_3278 : reg (bv 128)) (v_3279 : reg (bv 128)) => do
      v_5755 <- getRegister v_3278;
      v_5756 <- eval (extract v_5755 0 16);
      v_5761 <- eval (extract v_5755 16 32);
      v_5766 <- eval (extract v_5755 32 48);
      v_5771 <- eval (extract v_5755 48 64);
      v_5776 <- eval (extract v_5755 64 80);
      v_5781 <- eval (extract v_5755 80 96);
      v_5786 <- eval (extract v_5755 96 112);
      v_5791 <- eval (extract v_5755 112 128);
      setRegister (lhs.of_reg v_3279) (concat (mux (ugt v_5756 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5756 (expression.bv_nat 16 65535))) v_5756) (concat (mux (ugt v_5761 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5761 (expression.bv_nat 16 65535))) v_5761) (concat (mux (ugt v_5766 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5766 (expression.bv_nat 16 65535))) v_5766) (concat (mux (ugt v_5771 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5771 (expression.bv_nat 16 65535))) v_5771) (concat (mux (ugt v_5776 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5776 (expression.bv_nat 16 65535))) v_5776) (concat (mux (ugt v_5781 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5781 (expression.bv_nat 16 65535))) v_5781) (concat (mux (ugt v_5786 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5786 (expression.bv_nat 16 65535))) v_5786) (mux (ugt v_5791 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5791 (expression.bv_nat 16 65535))) v_5791))))))));
      pure ()
    pat_end;
    pattern fun (v_3288 : reg (bv 256)) (v_3289 : reg (bv 256)) => do
      v_5808 <- getRegister v_3288;
      v_5809 <- eval (extract v_5808 0 16);
      v_5814 <- eval (extract v_5808 16 32);
      v_5819 <- eval (extract v_5808 32 48);
      v_5824 <- eval (extract v_5808 48 64);
      v_5829 <- eval (extract v_5808 64 80);
      v_5834 <- eval (extract v_5808 80 96);
      v_5839 <- eval (extract v_5808 96 112);
      v_5844 <- eval (extract v_5808 112 128);
      v_5849 <- eval (extract v_5808 128 144);
      v_5854 <- eval (extract v_5808 144 160);
      v_5859 <- eval (extract v_5808 160 176);
      v_5864 <- eval (extract v_5808 176 192);
      v_5869 <- eval (extract v_5808 192 208);
      v_5874 <- eval (extract v_5808 208 224);
      v_5879 <- eval (extract v_5808 224 240);
      v_5884 <- eval (extract v_5808 240 256);
      setRegister (lhs.of_reg v_3289) (concat (mux (ugt v_5809 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5809 (expression.bv_nat 16 65535))) v_5809) (concat (mux (ugt v_5814 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5814 (expression.bv_nat 16 65535))) v_5814) (concat (mux (ugt v_5819 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5819 (expression.bv_nat 16 65535))) v_5819) (concat (mux (ugt v_5824 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5824 (expression.bv_nat 16 65535))) v_5824) (concat (mux (ugt v_5829 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5829 (expression.bv_nat 16 65535))) v_5829) (concat (mux (ugt v_5834 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5834 (expression.bv_nat 16 65535))) v_5834) (concat (mux (ugt v_5839 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5839 (expression.bv_nat 16 65535))) v_5839) (concat (mux (ugt v_5844 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5844 (expression.bv_nat 16 65535))) v_5844) (concat (mux (ugt v_5849 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5849 (expression.bv_nat 16 65535))) v_5849) (concat (mux (ugt v_5854 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5854 (expression.bv_nat 16 65535))) v_5854) (concat (mux (ugt v_5859 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5859 (expression.bv_nat 16 65535))) v_5859) (concat (mux (ugt v_5864 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5864 (expression.bv_nat 16 65535))) v_5864) (concat (mux (ugt v_5869 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5869 (expression.bv_nat 16 65535))) v_5869) (concat (mux (ugt v_5874 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5874 (expression.bv_nat 16 65535))) v_5874) (concat (mux (ugt v_5879 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5879 (expression.bv_nat 16 65535))) v_5879) (mux (ugt v_5884 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5884 (expression.bv_nat 16 65535))) v_5884))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3274 : Mem) (v_3275 : reg (bv 128)) => do
      v_10834 <- evaluateAddress v_3274;
      v_10835 <- load v_10834 16;
      v_10836 <- eval (extract v_10835 0 16);
      v_10841 <- eval (extract v_10835 16 32);
      v_10846 <- eval (extract v_10835 32 48);
      v_10851 <- eval (extract v_10835 48 64);
      v_10856 <- eval (extract v_10835 64 80);
      v_10861 <- eval (extract v_10835 80 96);
      v_10866 <- eval (extract v_10835 96 112);
      v_10871 <- eval (extract v_10835 112 128);
      setRegister (lhs.of_reg v_3275) (concat (mux (ugt v_10836 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10836 (expression.bv_nat 16 65535))) v_10836) (concat (mux (ugt v_10841 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10841 (expression.bv_nat 16 65535))) v_10841) (concat (mux (ugt v_10846 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10846 (expression.bv_nat 16 65535))) v_10846) (concat (mux (ugt v_10851 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10851 (expression.bv_nat 16 65535))) v_10851) (concat (mux (ugt v_10856 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10856 (expression.bv_nat 16 65535))) v_10856) (concat (mux (ugt v_10861 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10861 (expression.bv_nat 16 65535))) v_10861) (concat (mux (ugt v_10866 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10866 (expression.bv_nat 16 65535))) v_10866) (mux (ugt v_10871 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10871 (expression.bv_nat 16 65535))) v_10871))))))));
      pure ()
    pat_end;
    pattern fun (v_3283 : Mem) (v_3284 : reg (bv 256)) => do
      v_10884 <- evaluateAddress v_3283;
      v_10885 <- load v_10884 32;
      v_10886 <- eval (extract v_10885 0 16);
      v_10891 <- eval (extract v_10885 16 32);
      v_10896 <- eval (extract v_10885 32 48);
      v_10901 <- eval (extract v_10885 48 64);
      v_10906 <- eval (extract v_10885 64 80);
      v_10911 <- eval (extract v_10885 80 96);
      v_10916 <- eval (extract v_10885 96 112);
      v_10921 <- eval (extract v_10885 112 128);
      v_10926 <- eval (extract v_10885 128 144);
      v_10931 <- eval (extract v_10885 144 160);
      v_10936 <- eval (extract v_10885 160 176);
      v_10941 <- eval (extract v_10885 176 192);
      v_10946 <- eval (extract v_10885 192 208);
      v_10951 <- eval (extract v_10885 208 224);
      v_10956 <- eval (extract v_10885 224 240);
      v_10961 <- eval (extract v_10885 240 256);
      setRegister (lhs.of_reg v_3284) (concat (mux (ugt v_10886 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10886 (expression.bv_nat 16 65535))) v_10886) (concat (mux (ugt v_10891 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10891 (expression.bv_nat 16 65535))) v_10891) (concat (mux (ugt v_10896 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10896 (expression.bv_nat 16 65535))) v_10896) (concat (mux (ugt v_10901 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10901 (expression.bv_nat 16 65535))) v_10901) (concat (mux (ugt v_10906 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10906 (expression.bv_nat 16 65535))) v_10906) (concat (mux (ugt v_10911 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10911 (expression.bv_nat 16 65535))) v_10911) (concat (mux (ugt v_10916 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10916 (expression.bv_nat 16 65535))) v_10916) (concat (mux (ugt v_10921 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10921 (expression.bv_nat 16 65535))) v_10921) (concat (mux (ugt v_10926 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10926 (expression.bv_nat 16 65535))) v_10926) (concat (mux (ugt v_10931 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10931 (expression.bv_nat 16 65535))) v_10931) (concat (mux (ugt v_10936 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10936 (expression.bv_nat 16 65535))) v_10936) (concat (mux (ugt v_10941 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10941 (expression.bv_nat 16 65535))) v_10941) (concat (mux (ugt v_10946 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10946 (expression.bv_nat 16 65535))) v_10946) (concat (mux (ugt v_10951 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10951 (expression.bv_nat 16 65535))) v_10951) (concat (mux (ugt v_10956 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10956 (expression.bv_nat 16 65535))) v_10956) (mux (ugt v_10961 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10961 (expression.bv_nat 16 65535))) v_10961))))))))))))))));
      pure ()
    pat_end
