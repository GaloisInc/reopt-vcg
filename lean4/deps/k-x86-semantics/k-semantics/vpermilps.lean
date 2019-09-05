def vpermilps1 : instruction :=
  definst "vpermilps" $ do
    pattern fun (v_3080 : imm int) (v_3082 : reg (bv 128)) (v_3083 : reg (bv 128)) => do
      v_8232 <- eval (handleImmediateWithSignExtend v_3080 8 8);
      v_8233 <- eval (extract v_8232 0 2);
      v_8235 <- getRegister v_3082;
      v_8236 <- eval (extract v_8235 96 128);
      v_8238 <- eval (extract v_8235 64 96);
      v_8240 <- eval (extract v_8235 32 64);
      v_8241 <- eval (extract v_8235 0 32);
      v_8245 <- eval (extract v_8232 2 4);
      v_8252 <- eval (extract v_8232 4 6);
      v_8259 <- eval (extract v_8232 6 8);
      setRegister (lhs.of_reg v_3083) (concat (mux (eq v_8233 (expression.bv_nat 2 0)) v_8236 (mux (eq v_8233 (expression.bv_nat 2 1)) v_8238 (mux (eq v_8233 (expression.bv_nat 2 2)) v_8240 v_8241))) (concat (mux (eq v_8245 (expression.bv_nat 2 0)) v_8236 (mux (eq v_8245 (expression.bv_nat 2 1)) v_8238 (mux (eq v_8245 (expression.bv_nat 2 2)) v_8240 v_8241))) (concat (mux (eq v_8252 (expression.bv_nat 2 0)) v_8236 (mux (eq v_8252 (expression.bv_nat 2 1)) v_8238 (mux (eq v_8252 (expression.bv_nat 2 2)) v_8240 v_8241))) (mux (eq v_8259 (expression.bv_nat 2 0)) v_8236 (mux (eq v_8259 (expression.bv_nat 2 1)) v_8238 (mux (eq v_8259 (expression.bv_nat 2 2)) v_8240 v_8241))))));
      pure ()
    pat_end;
    pattern fun (v_3092 : reg (bv 128)) (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_8275 <- getRegister v_3092;
      v_8276 <- eval (extract v_8275 30 32);
      v_8278 <- getRegister v_3093;
      v_8279 <- eval (extract v_8278 96 128);
      v_8281 <- eval (extract v_8278 64 96);
      v_8283 <- eval (extract v_8278 32 64);
      v_8284 <- eval (extract v_8278 0 32);
      v_8288 <- eval (extract v_8275 62 64);
      v_8295 <- eval (extract v_8275 94 96);
      v_8302 <- eval (extract v_8275 126 128);
      setRegister (lhs.of_reg v_3094) (concat (mux (eq v_8276 (expression.bv_nat 2 0)) v_8279 (mux (eq v_8276 (expression.bv_nat 2 1)) v_8281 (mux (eq v_8276 (expression.bv_nat 2 2)) v_8283 v_8284))) (concat (mux (eq v_8288 (expression.bv_nat 2 0)) v_8279 (mux (eq v_8288 (expression.bv_nat 2 1)) v_8281 (mux (eq v_8288 (expression.bv_nat 2 2)) v_8283 v_8284))) (concat (mux (eq v_8295 (expression.bv_nat 2 0)) v_8279 (mux (eq v_8295 (expression.bv_nat 2 1)) v_8281 (mux (eq v_8295 (expression.bv_nat 2 2)) v_8283 v_8284))) (mux (eq v_8302 (expression.bv_nat 2 0)) v_8279 (mux (eq v_8302 (expression.bv_nat 2 1)) v_8281 (mux (eq v_8302 (expression.bv_nat 2 2)) v_8283 v_8284))))));
      pure ()
    pat_end;
    pattern fun (v_3102 : imm int) (v_3103 : reg (bv 256)) (v_3104 : reg (bv 256)) => do
      v_8318 <- eval (handleImmediateWithSignExtend v_3102 8 8);
      v_8319 <- eval (extract v_8318 0 2);
      v_8320 <- eval (eq v_8319 (expression.bv_nat 2 0));
      v_8321 <- getRegister v_3103;
      v_8322 <- eval (extract v_8321 96 128);
      v_8323 <- eval (eq v_8319 (expression.bv_nat 2 1));
      v_8324 <- eval (extract v_8321 64 96);
      v_8325 <- eval (eq v_8319 (expression.bv_nat 2 2));
      v_8326 <- eval (extract v_8321 32 64);
      v_8327 <- eval (extract v_8321 0 32);
      v_8331 <- eval (extract v_8318 2 4);
      v_8332 <- eval (eq v_8331 (expression.bv_nat 2 0));
      v_8333 <- eval (eq v_8331 (expression.bv_nat 2 1));
      v_8334 <- eval (eq v_8331 (expression.bv_nat 2 2));
      v_8338 <- eval (extract v_8318 4 6);
      v_8339 <- eval (eq v_8338 (expression.bv_nat 2 0));
      v_8340 <- eval (eq v_8338 (expression.bv_nat 2 1));
      v_8341 <- eval (eq v_8338 (expression.bv_nat 2 2));
      v_8345 <- eval (extract v_8318 6 8);
      v_8346 <- eval (eq v_8345 (expression.bv_nat 2 0));
      v_8347 <- eval (eq v_8345 (expression.bv_nat 2 1));
      v_8348 <- eval (eq v_8345 (expression.bv_nat 2 2));
      v_8352 <- eval (extract v_8321 224 256);
      v_8353 <- eval (extract v_8321 192 224);
      v_8354 <- eval (extract v_8321 160 192);
      v_8355 <- eval (extract v_8321 128 160);
      setRegister (lhs.of_reg v_3104) (concat (mux v_8320 v_8322 (mux v_8323 v_8324 (mux v_8325 v_8326 v_8327))) (concat (mux v_8332 v_8322 (mux v_8333 v_8324 (mux v_8334 v_8326 v_8327))) (concat (mux v_8339 v_8322 (mux v_8340 v_8324 (mux v_8341 v_8326 v_8327))) (concat (mux v_8346 v_8322 (mux v_8347 v_8324 (mux v_8348 v_8326 v_8327))) (concat (mux v_8320 v_8352 (mux v_8323 v_8353 (mux v_8325 v_8354 v_8355))) (concat (mux v_8332 v_8352 (mux v_8333 v_8353 (mux v_8334 v_8354 v_8355))) (concat (mux v_8339 v_8352 (mux v_8340 v_8353 (mux v_8341 v_8354 v_8355))) (mux v_8346 v_8352 (mux v_8347 v_8353 (mux v_8348 v_8354 v_8355))))))))));
      pure ()
    pat_end;
    pattern fun (v_3113 : reg (bv 256)) (v_3114 : reg (bv 256)) (v_3115 : reg (bv 256)) => do
      v_8381 <- getRegister v_3113;
      v_8382 <- eval (extract v_8381 30 32);
      v_8384 <- getRegister v_3114;
      v_8385 <- eval (extract v_8384 96 128);
      v_8387 <- eval (extract v_8384 64 96);
      v_8389 <- eval (extract v_8384 32 64);
      v_8390 <- eval (extract v_8384 0 32);
      v_8394 <- eval (extract v_8381 62 64);
      v_8401 <- eval (extract v_8381 94 96);
      v_8408 <- eval (extract v_8381 126 128);
      v_8415 <- eval (extract v_8381 158 160);
      v_8417 <- eval (extract v_8384 224 256);
      v_8419 <- eval (extract v_8384 192 224);
      v_8421 <- eval (extract v_8384 160 192);
      v_8422 <- eval (extract v_8384 128 160);
      v_8426 <- eval (extract v_8381 190 192);
      v_8433 <- eval (extract v_8381 222 224);
      v_8440 <- eval (extract v_8381 254 256);
      setRegister (lhs.of_reg v_3115) (concat (mux (eq v_8382 (expression.bv_nat 2 0)) v_8385 (mux (eq v_8382 (expression.bv_nat 2 1)) v_8387 (mux (eq v_8382 (expression.bv_nat 2 2)) v_8389 v_8390))) (concat (mux (eq v_8394 (expression.bv_nat 2 0)) v_8385 (mux (eq v_8394 (expression.bv_nat 2 1)) v_8387 (mux (eq v_8394 (expression.bv_nat 2 2)) v_8389 v_8390))) (concat (mux (eq v_8401 (expression.bv_nat 2 0)) v_8385 (mux (eq v_8401 (expression.bv_nat 2 1)) v_8387 (mux (eq v_8401 (expression.bv_nat 2 2)) v_8389 v_8390))) (concat (mux (eq v_8408 (expression.bv_nat 2 0)) v_8385 (mux (eq v_8408 (expression.bv_nat 2 1)) v_8387 (mux (eq v_8408 (expression.bv_nat 2 2)) v_8389 v_8390))) (concat (mux (eq v_8415 (expression.bv_nat 2 0)) v_8417 (mux (eq v_8415 (expression.bv_nat 2 1)) v_8419 (mux (eq v_8415 (expression.bv_nat 2 2)) v_8421 v_8422))) (concat (mux (eq v_8426 (expression.bv_nat 2 0)) v_8417 (mux (eq v_8426 (expression.bv_nat 2 1)) v_8419 (mux (eq v_8426 (expression.bv_nat 2 2)) v_8421 v_8422))) (concat (mux (eq v_8433 (expression.bv_nat 2 0)) v_8417 (mux (eq v_8433 (expression.bv_nat 2 1)) v_8419 (mux (eq v_8433 (expression.bv_nat 2 2)) v_8421 v_8422))) (mux (eq v_8440 (expression.bv_nat 2 0)) v_8417 (mux (eq v_8440 (expression.bv_nat 2 1)) v_8419 (mux (eq v_8440 (expression.bv_nat 2 2)) v_8421 v_8422))))))))));
      pure ()
    pat_end;
    pattern fun (v_3075 : imm int) (v_3076 : Mem) (v_3077 : reg (bv 128)) => do
      v_16754 <- eval (handleImmediateWithSignExtend v_3075 8 8);
      v_16755 <- eval (extract v_16754 0 2);
      v_16757 <- evaluateAddress v_3076;
      v_16758 <- load v_16757 16;
      v_16759 <- eval (extract v_16758 96 128);
      v_16761 <- eval (extract v_16758 64 96);
      v_16763 <- eval (extract v_16758 32 64);
      v_16764 <- eval (extract v_16758 0 32);
      v_16768 <- eval (extract v_16754 2 4);
      v_16775 <- eval (extract v_16754 4 6);
      v_16782 <- eval (extract v_16754 6 8);
      setRegister (lhs.of_reg v_3077) (concat (mux (eq v_16755 (expression.bv_nat 2 0)) v_16759 (mux (eq v_16755 (expression.bv_nat 2 1)) v_16761 (mux (eq v_16755 (expression.bv_nat 2 2)) v_16763 v_16764))) (concat (mux (eq v_16768 (expression.bv_nat 2 0)) v_16759 (mux (eq v_16768 (expression.bv_nat 2 1)) v_16761 (mux (eq v_16768 (expression.bv_nat 2 2)) v_16763 v_16764))) (concat (mux (eq v_16775 (expression.bv_nat 2 0)) v_16759 (mux (eq v_16775 (expression.bv_nat 2 1)) v_16761 (mux (eq v_16775 (expression.bv_nat 2 2)) v_16763 v_16764))) (mux (eq v_16782 (expression.bv_nat 2 0)) v_16759 (mux (eq v_16782 (expression.bv_nat 2 1)) v_16761 (mux (eq v_16782 (expression.bv_nat 2 2)) v_16763 v_16764))))));
      pure ()
    pat_end;
    pattern fun (v_3086 : Mem) (v_3087 : reg (bv 128)) (v_3088 : reg (bv 128)) => do
      v_16793 <- evaluateAddress v_3086;
      v_16794 <- load v_16793 16;
      v_16795 <- eval (extract v_16794 30 32);
      v_16797 <- getRegister v_3087;
      v_16798 <- eval (extract v_16797 96 128);
      v_16800 <- eval (extract v_16797 64 96);
      v_16802 <- eval (extract v_16797 32 64);
      v_16803 <- eval (extract v_16797 0 32);
      v_16807 <- eval (extract v_16794 62 64);
      v_16814 <- eval (extract v_16794 94 96);
      v_16821 <- eval (extract v_16794 126 128);
      setRegister (lhs.of_reg v_3088) (concat (mux (eq v_16795 (expression.bv_nat 2 0)) v_16798 (mux (eq v_16795 (expression.bv_nat 2 1)) v_16800 (mux (eq v_16795 (expression.bv_nat 2 2)) v_16802 v_16803))) (concat (mux (eq v_16807 (expression.bv_nat 2 0)) v_16798 (mux (eq v_16807 (expression.bv_nat 2 1)) v_16800 (mux (eq v_16807 (expression.bv_nat 2 2)) v_16802 v_16803))) (concat (mux (eq v_16814 (expression.bv_nat 2 0)) v_16798 (mux (eq v_16814 (expression.bv_nat 2 1)) v_16800 (mux (eq v_16814 (expression.bv_nat 2 2)) v_16802 v_16803))) (mux (eq v_16821 (expression.bv_nat 2 0)) v_16798 (mux (eq v_16821 (expression.bv_nat 2 1)) v_16800 (mux (eq v_16821 (expression.bv_nat 2 2)) v_16802 v_16803))))));
      pure ()
    pat_end;
    pattern fun (v_3097 : imm int) (v_3098 : Mem) (v_3099 : reg (bv 256)) => do
      v_16832 <- eval (handleImmediateWithSignExtend v_3097 8 8);
      v_16833 <- eval (extract v_16832 0 2);
      v_16834 <- eval (eq v_16833 (expression.bv_nat 2 0));
      v_16835 <- evaluateAddress v_3098;
      v_16836 <- load v_16835 32;
      v_16837 <- eval (extract v_16836 96 128);
      v_16838 <- eval (eq v_16833 (expression.bv_nat 2 1));
      v_16839 <- eval (extract v_16836 64 96);
      v_16840 <- eval (eq v_16833 (expression.bv_nat 2 2));
      v_16841 <- eval (extract v_16836 32 64);
      v_16842 <- eval (extract v_16836 0 32);
      v_16846 <- eval (extract v_16832 2 4);
      v_16847 <- eval (eq v_16846 (expression.bv_nat 2 0));
      v_16848 <- eval (eq v_16846 (expression.bv_nat 2 1));
      v_16849 <- eval (eq v_16846 (expression.bv_nat 2 2));
      v_16853 <- eval (extract v_16832 4 6);
      v_16854 <- eval (eq v_16853 (expression.bv_nat 2 0));
      v_16855 <- eval (eq v_16853 (expression.bv_nat 2 1));
      v_16856 <- eval (eq v_16853 (expression.bv_nat 2 2));
      v_16860 <- eval (extract v_16832 6 8);
      v_16861 <- eval (eq v_16860 (expression.bv_nat 2 0));
      v_16862 <- eval (eq v_16860 (expression.bv_nat 2 1));
      v_16863 <- eval (eq v_16860 (expression.bv_nat 2 2));
      v_16867 <- eval (extract v_16836 224 256);
      v_16868 <- eval (extract v_16836 192 224);
      v_16869 <- eval (extract v_16836 160 192);
      v_16870 <- eval (extract v_16836 128 160);
      setRegister (lhs.of_reg v_3099) (concat (mux v_16834 v_16837 (mux v_16838 v_16839 (mux v_16840 v_16841 v_16842))) (concat (mux v_16847 v_16837 (mux v_16848 v_16839 (mux v_16849 v_16841 v_16842))) (concat (mux v_16854 v_16837 (mux v_16855 v_16839 (mux v_16856 v_16841 v_16842))) (concat (mux v_16861 v_16837 (mux v_16862 v_16839 (mux v_16863 v_16841 v_16842))) (concat (mux v_16834 v_16867 (mux v_16838 v_16868 (mux v_16840 v_16869 v_16870))) (concat (mux v_16847 v_16867 (mux v_16848 v_16868 (mux v_16849 v_16869 v_16870))) (concat (mux v_16854 v_16867 (mux v_16855 v_16868 (mux v_16856 v_16869 v_16870))) (mux v_16861 v_16867 (mux v_16862 v_16868 (mux v_16863 v_16869 v_16870))))))))));
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) (v_3109 : reg (bv 256)) (v_3110 : reg (bv 256)) => do
      v_16891 <- evaluateAddress v_3108;
      v_16892 <- load v_16891 32;
      v_16893 <- eval (extract v_16892 30 32);
      v_16895 <- getRegister v_3109;
      v_16896 <- eval (extract v_16895 96 128);
      v_16898 <- eval (extract v_16895 64 96);
      v_16900 <- eval (extract v_16895 32 64);
      v_16901 <- eval (extract v_16895 0 32);
      v_16905 <- eval (extract v_16892 62 64);
      v_16912 <- eval (extract v_16892 94 96);
      v_16919 <- eval (extract v_16892 126 128);
      v_16926 <- eval (extract v_16892 158 160);
      v_16928 <- eval (extract v_16895 224 256);
      v_16930 <- eval (extract v_16895 192 224);
      v_16932 <- eval (extract v_16895 160 192);
      v_16933 <- eval (extract v_16895 128 160);
      v_16937 <- eval (extract v_16892 190 192);
      v_16944 <- eval (extract v_16892 222 224);
      v_16951 <- eval (extract v_16892 254 256);
      setRegister (lhs.of_reg v_3110) (concat (mux (eq v_16893 (expression.bv_nat 2 0)) v_16896 (mux (eq v_16893 (expression.bv_nat 2 1)) v_16898 (mux (eq v_16893 (expression.bv_nat 2 2)) v_16900 v_16901))) (concat (mux (eq v_16905 (expression.bv_nat 2 0)) v_16896 (mux (eq v_16905 (expression.bv_nat 2 1)) v_16898 (mux (eq v_16905 (expression.bv_nat 2 2)) v_16900 v_16901))) (concat (mux (eq v_16912 (expression.bv_nat 2 0)) v_16896 (mux (eq v_16912 (expression.bv_nat 2 1)) v_16898 (mux (eq v_16912 (expression.bv_nat 2 2)) v_16900 v_16901))) (concat (mux (eq v_16919 (expression.bv_nat 2 0)) v_16896 (mux (eq v_16919 (expression.bv_nat 2 1)) v_16898 (mux (eq v_16919 (expression.bv_nat 2 2)) v_16900 v_16901))) (concat (mux (eq v_16926 (expression.bv_nat 2 0)) v_16928 (mux (eq v_16926 (expression.bv_nat 2 1)) v_16930 (mux (eq v_16926 (expression.bv_nat 2 2)) v_16932 v_16933))) (concat (mux (eq v_16937 (expression.bv_nat 2 0)) v_16928 (mux (eq v_16937 (expression.bv_nat 2 1)) v_16930 (mux (eq v_16937 (expression.bv_nat 2 2)) v_16932 v_16933))) (concat (mux (eq v_16944 (expression.bv_nat 2 0)) v_16928 (mux (eq v_16944 (expression.bv_nat 2 1)) v_16930 (mux (eq v_16944 (expression.bv_nat 2 2)) v_16932 v_16933))) (mux (eq v_16951 (expression.bv_nat 2 0)) v_16928 (mux (eq v_16951 (expression.bv_nat 2 1)) v_16930 (mux (eq v_16951 (expression.bv_nat 2 2)) v_16932 v_16933))))))))));
      pure ()
    pat_end
