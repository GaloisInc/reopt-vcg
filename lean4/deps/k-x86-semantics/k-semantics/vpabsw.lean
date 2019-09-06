def vpabsw1 : instruction :=
  definst "vpabsw" $ do
    pattern fun (v_3303 : reg (bv 128)) (v_3304 : reg (bv 128)) => do
      v_5782 <- getRegister v_3303;
      v_5783 <- eval (extract v_5782 0 16);
      v_5788 <- eval (extract v_5782 16 32);
      v_5793 <- eval (extract v_5782 32 48);
      v_5798 <- eval (extract v_5782 48 64);
      v_5803 <- eval (extract v_5782 64 80);
      v_5808 <- eval (extract v_5782 80 96);
      v_5813 <- eval (extract v_5782 96 112);
      v_5818 <- eval (extract v_5782 112 128);
      setRegister (lhs.of_reg v_3304) (concat (mux (ugt v_5783 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5783 (expression.bv_nat 16 65535))) v_5783) (concat (mux (ugt v_5788 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5788 (expression.bv_nat 16 65535))) v_5788) (concat (mux (ugt v_5793 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5793 (expression.bv_nat 16 65535))) v_5793) (concat (mux (ugt v_5798 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5798 (expression.bv_nat 16 65535))) v_5798) (concat (mux (ugt v_5803 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5803 (expression.bv_nat 16 65535))) v_5803) (concat (mux (ugt v_5808 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5808 (expression.bv_nat 16 65535))) v_5808) (concat (mux (ugt v_5813 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5813 (expression.bv_nat 16 65535))) v_5813) (mux (ugt v_5818 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5818 (expression.bv_nat 16 65535))) v_5818))))))));
      pure ()
    pat_end;
    pattern fun (v_3312 : reg (bv 256)) (v_3313 : reg (bv 256)) => do
      v_5835 <- getRegister v_3312;
      v_5836 <- eval (extract v_5835 0 16);
      v_5841 <- eval (extract v_5835 16 32);
      v_5846 <- eval (extract v_5835 32 48);
      v_5851 <- eval (extract v_5835 48 64);
      v_5856 <- eval (extract v_5835 64 80);
      v_5861 <- eval (extract v_5835 80 96);
      v_5866 <- eval (extract v_5835 96 112);
      v_5871 <- eval (extract v_5835 112 128);
      v_5876 <- eval (extract v_5835 128 144);
      v_5881 <- eval (extract v_5835 144 160);
      v_5886 <- eval (extract v_5835 160 176);
      v_5891 <- eval (extract v_5835 176 192);
      v_5896 <- eval (extract v_5835 192 208);
      v_5901 <- eval (extract v_5835 208 224);
      v_5906 <- eval (extract v_5835 224 240);
      v_5911 <- eval (extract v_5835 240 256);
      setRegister (lhs.of_reg v_3313) (concat (mux (ugt v_5836 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5836 (expression.bv_nat 16 65535))) v_5836) (concat (mux (ugt v_5841 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5841 (expression.bv_nat 16 65535))) v_5841) (concat (mux (ugt v_5846 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5846 (expression.bv_nat 16 65535))) v_5846) (concat (mux (ugt v_5851 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5851 (expression.bv_nat 16 65535))) v_5851) (concat (mux (ugt v_5856 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5856 (expression.bv_nat 16 65535))) v_5856) (concat (mux (ugt v_5861 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5861 (expression.bv_nat 16 65535))) v_5861) (concat (mux (ugt v_5866 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5866 (expression.bv_nat 16 65535))) v_5866) (concat (mux (ugt v_5871 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5871 (expression.bv_nat 16 65535))) v_5871) (concat (mux (ugt v_5876 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5876 (expression.bv_nat 16 65535))) v_5876) (concat (mux (ugt v_5881 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5881 (expression.bv_nat 16 65535))) v_5881) (concat (mux (ugt v_5886 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5886 (expression.bv_nat 16 65535))) v_5886) (concat (mux (ugt v_5891 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5891 (expression.bv_nat 16 65535))) v_5891) (concat (mux (ugt v_5896 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5896 (expression.bv_nat 16 65535))) v_5896) (concat (mux (ugt v_5901 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5901 (expression.bv_nat 16 65535))) v_5901) (concat (mux (ugt v_5906 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5906 (expression.bv_nat 16 65535))) v_5906) (mux (ugt v_5911 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5911 (expression.bv_nat 16 65535))) v_5911))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3299 : Mem) (v_3300 : reg (bv 128)) => do
      v_10861 <- evaluateAddress v_3299;
      v_10862 <- load v_10861 16;
      v_10863 <- eval (extract v_10862 0 16);
      v_10868 <- eval (extract v_10862 16 32);
      v_10873 <- eval (extract v_10862 32 48);
      v_10878 <- eval (extract v_10862 48 64);
      v_10883 <- eval (extract v_10862 64 80);
      v_10888 <- eval (extract v_10862 80 96);
      v_10893 <- eval (extract v_10862 96 112);
      v_10898 <- eval (extract v_10862 112 128);
      setRegister (lhs.of_reg v_3300) (concat (mux (ugt v_10863 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10863 (expression.bv_nat 16 65535))) v_10863) (concat (mux (ugt v_10868 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10868 (expression.bv_nat 16 65535))) v_10868) (concat (mux (ugt v_10873 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10873 (expression.bv_nat 16 65535))) v_10873) (concat (mux (ugt v_10878 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10878 (expression.bv_nat 16 65535))) v_10878) (concat (mux (ugt v_10883 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10883 (expression.bv_nat 16 65535))) v_10883) (concat (mux (ugt v_10888 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10888 (expression.bv_nat 16 65535))) v_10888) (concat (mux (ugt v_10893 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10893 (expression.bv_nat 16 65535))) v_10893) (mux (ugt v_10898 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10898 (expression.bv_nat 16 65535))) v_10898))))))));
      pure ()
    pat_end;
    pattern fun (v_3308 : Mem) (v_3309 : reg (bv 256)) => do
      v_10911 <- evaluateAddress v_3308;
      v_10912 <- load v_10911 32;
      v_10913 <- eval (extract v_10912 0 16);
      v_10918 <- eval (extract v_10912 16 32);
      v_10923 <- eval (extract v_10912 32 48);
      v_10928 <- eval (extract v_10912 48 64);
      v_10933 <- eval (extract v_10912 64 80);
      v_10938 <- eval (extract v_10912 80 96);
      v_10943 <- eval (extract v_10912 96 112);
      v_10948 <- eval (extract v_10912 112 128);
      v_10953 <- eval (extract v_10912 128 144);
      v_10958 <- eval (extract v_10912 144 160);
      v_10963 <- eval (extract v_10912 160 176);
      v_10968 <- eval (extract v_10912 176 192);
      v_10973 <- eval (extract v_10912 192 208);
      v_10978 <- eval (extract v_10912 208 224);
      v_10983 <- eval (extract v_10912 224 240);
      v_10988 <- eval (extract v_10912 240 256);
      setRegister (lhs.of_reg v_3309) (concat (mux (ugt v_10913 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10913 (expression.bv_nat 16 65535))) v_10913) (concat (mux (ugt v_10918 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10918 (expression.bv_nat 16 65535))) v_10918) (concat (mux (ugt v_10923 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10923 (expression.bv_nat 16 65535))) v_10923) (concat (mux (ugt v_10928 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10928 (expression.bv_nat 16 65535))) v_10928) (concat (mux (ugt v_10933 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10933 (expression.bv_nat 16 65535))) v_10933) (concat (mux (ugt v_10938 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10938 (expression.bv_nat 16 65535))) v_10938) (concat (mux (ugt v_10943 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10943 (expression.bv_nat 16 65535))) v_10943) (concat (mux (ugt v_10948 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10948 (expression.bv_nat 16 65535))) v_10948) (concat (mux (ugt v_10953 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10953 (expression.bv_nat 16 65535))) v_10953) (concat (mux (ugt v_10958 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10958 (expression.bv_nat 16 65535))) v_10958) (concat (mux (ugt v_10963 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10963 (expression.bv_nat 16 65535))) v_10963) (concat (mux (ugt v_10968 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10968 (expression.bv_nat 16 65535))) v_10968) (concat (mux (ugt v_10973 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10973 (expression.bv_nat 16 65535))) v_10973) (concat (mux (ugt v_10978 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10978 (expression.bv_nat 16 65535))) v_10978) (concat (mux (ugt v_10983 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10983 (expression.bv_nat 16 65535))) v_10983) (mux (ugt v_10988 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10988 (expression.bv_nat 16 65535))) v_10988))))))))))))))));
      pure ()
    pat_end
