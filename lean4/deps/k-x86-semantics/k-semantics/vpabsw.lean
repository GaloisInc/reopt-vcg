def vpabsw1 : instruction :=
  definst "vpabsw" $ do
    pattern fun (v_3215 : reg (bv 128)) (v_3216 : reg (bv 128)) => do
      v_5817 <- getRegister v_3215;
      v_5818 <- eval (extract v_5817 0 16);
      v_5825 <- eval (extract v_5817 16 32);
      v_5832 <- eval (extract v_5817 32 48);
      v_5839 <- eval (extract v_5817 48 64);
      v_5846 <- eval (extract v_5817 64 80);
      v_5853 <- eval (extract v_5817 80 96);
      v_5860 <- eval (extract v_5817 96 112);
      v_5867 <- eval (extract v_5817 112 128);
      setRegister (lhs.of_reg v_3216) (concat (mux (ugt v_5818 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5818 (mi (bitwidthMInt v_5818) -1))) v_5818) (concat (mux (ugt v_5825 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5825 (mi (bitwidthMInt v_5825) -1))) v_5825) (concat (mux (ugt v_5832 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5832 (mi (bitwidthMInt v_5832) -1))) v_5832) (concat (mux (ugt v_5839 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5839 (mi (bitwidthMInt v_5839) -1))) v_5839) (concat (mux (ugt v_5846 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5846 (mi (bitwidthMInt v_5846) -1))) v_5846) (concat (mux (ugt v_5853 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5853 (mi (bitwidthMInt v_5853) -1))) v_5853) (concat (mux (ugt v_5860 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5860 (mi (bitwidthMInt v_5860) -1))) v_5860) (mux (ugt v_5867 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5867 (mi (bitwidthMInt v_5867) -1))) v_5867))))))));
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 256)) (v_3225 : reg (bv 256)) => do
      v_5886 <- getRegister v_3224;
      v_5887 <- eval (extract v_5886 0 16);
      v_5894 <- eval (extract v_5886 16 32);
      v_5901 <- eval (extract v_5886 32 48);
      v_5908 <- eval (extract v_5886 48 64);
      v_5915 <- eval (extract v_5886 64 80);
      v_5922 <- eval (extract v_5886 80 96);
      v_5929 <- eval (extract v_5886 96 112);
      v_5936 <- eval (extract v_5886 112 128);
      v_5943 <- eval (extract v_5886 128 144);
      v_5950 <- eval (extract v_5886 144 160);
      v_5957 <- eval (extract v_5886 160 176);
      v_5964 <- eval (extract v_5886 176 192);
      v_5971 <- eval (extract v_5886 192 208);
      v_5978 <- eval (extract v_5886 208 224);
      v_5985 <- eval (extract v_5886 224 240);
      v_5992 <- eval (extract v_5886 240 256);
      setRegister (lhs.of_reg v_3225) (concat (mux (ugt v_5887 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5887 (mi (bitwidthMInt v_5887) -1))) v_5887) (concat (mux (ugt v_5894 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5894 (mi (bitwidthMInt v_5894) -1))) v_5894) (concat (mux (ugt v_5901 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5901 (mi (bitwidthMInt v_5901) -1))) v_5901) (concat (mux (ugt v_5908 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5908 (mi (bitwidthMInt v_5908) -1))) v_5908) (concat (mux (ugt v_5915 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5915 (mi (bitwidthMInt v_5915) -1))) v_5915) (concat (mux (ugt v_5922 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5922 (mi (bitwidthMInt v_5922) -1))) v_5922) (concat (mux (ugt v_5929 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5929 (mi (bitwidthMInt v_5929) -1))) v_5929) (concat (mux (ugt v_5936 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5936 (mi (bitwidthMInt v_5936) -1))) v_5936) (concat (mux (ugt v_5943 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5943 (mi (bitwidthMInt v_5943) -1))) v_5943) (concat (mux (ugt v_5950 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5950 (mi (bitwidthMInt v_5950) -1))) v_5950) (concat (mux (ugt v_5957 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5957 (mi (bitwidthMInt v_5957) -1))) v_5957) (concat (mux (ugt v_5964 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5964 (mi (bitwidthMInt v_5964) -1))) v_5964) (concat (mux (ugt v_5971 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5971 (mi (bitwidthMInt v_5971) -1))) v_5971) (concat (mux (ugt v_5978 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5978 (mi (bitwidthMInt v_5978) -1))) v_5978) (concat (mux (ugt v_5985 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5985 (mi (bitwidthMInt v_5985) -1))) v_5985) (mux (ugt v_5992 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5992 (mi (bitwidthMInt v_5992) -1))) v_5992))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3210 : Mem) (v_3211 : reg (bv 128)) => do
      v_11088 <- evaluateAddress v_3210;
      v_11089 <- load v_11088 16;
      v_11090 <- eval (extract v_11089 0 16);
      v_11097 <- eval (extract v_11089 16 32);
      v_11104 <- eval (extract v_11089 32 48);
      v_11111 <- eval (extract v_11089 48 64);
      v_11118 <- eval (extract v_11089 64 80);
      v_11125 <- eval (extract v_11089 80 96);
      v_11132 <- eval (extract v_11089 96 112);
      v_11139 <- eval (extract v_11089 112 128);
      setRegister (lhs.of_reg v_3211) (concat (mux (ugt v_11090 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11090 (mi (bitwidthMInt v_11090) -1))) v_11090) (concat (mux (ugt v_11097 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11097 (mi (bitwidthMInt v_11097) -1))) v_11097) (concat (mux (ugt v_11104 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11104 (mi (bitwidthMInt v_11104) -1))) v_11104) (concat (mux (ugt v_11111 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11111 (mi (bitwidthMInt v_11111) -1))) v_11111) (concat (mux (ugt v_11118 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11118 (mi (bitwidthMInt v_11118) -1))) v_11118) (concat (mux (ugt v_11125 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11125 (mi (bitwidthMInt v_11125) -1))) v_11125) (concat (mux (ugt v_11132 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11132 (mi (bitwidthMInt v_11132) -1))) v_11132) (mux (ugt v_11139 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11139 (mi (bitwidthMInt v_11139) -1))) v_11139))))))));
      pure ()
    pat_end;
    pattern fun (v_3219 : Mem) (v_3220 : reg (bv 256)) => do
      v_11154 <- evaluateAddress v_3219;
      v_11155 <- load v_11154 32;
      v_11156 <- eval (extract v_11155 0 16);
      v_11163 <- eval (extract v_11155 16 32);
      v_11170 <- eval (extract v_11155 32 48);
      v_11177 <- eval (extract v_11155 48 64);
      v_11184 <- eval (extract v_11155 64 80);
      v_11191 <- eval (extract v_11155 80 96);
      v_11198 <- eval (extract v_11155 96 112);
      v_11205 <- eval (extract v_11155 112 128);
      v_11212 <- eval (extract v_11155 128 144);
      v_11219 <- eval (extract v_11155 144 160);
      v_11226 <- eval (extract v_11155 160 176);
      v_11233 <- eval (extract v_11155 176 192);
      v_11240 <- eval (extract v_11155 192 208);
      v_11247 <- eval (extract v_11155 208 224);
      v_11254 <- eval (extract v_11155 224 240);
      v_11261 <- eval (extract v_11155 240 256);
      setRegister (lhs.of_reg v_3220) (concat (mux (ugt v_11156 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11156 (mi (bitwidthMInt v_11156) -1))) v_11156) (concat (mux (ugt v_11163 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11163 (mi (bitwidthMInt v_11163) -1))) v_11163) (concat (mux (ugt v_11170 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11170 (mi (bitwidthMInt v_11170) -1))) v_11170) (concat (mux (ugt v_11177 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11177 (mi (bitwidthMInt v_11177) -1))) v_11177) (concat (mux (ugt v_11184 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11184 (mi (bitwidthMInt v_11184) -1))) v_11184) (concat (mux (ugt v_11191 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11191 (mi (bitwidthMInt v_11191) -1))) v_11191) (concat (mux (ugt v_11198 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11198 (mi (bitwidthMInt v_11198) -1))) v_11198) (concat (mux (ugt v_11205 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11205 (mi (bitwidthMInt v_11205) -1))) v_11205) (concat (mux (ugt v_11212 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11212 (mi (bitwidthMInt v_11212) -1))) v_11212) (concat (mux (ugt v_11219 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11219 (mi (bitwidthMInt v_11219) -1))) v_11219) (concat (mux (ugt v_11226 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11226 (mi (bitwidthMInt v_11226) -1))) v_11226) (concat (mux (ugt v_11233 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11233 (mi (bitwidthMInt v_11233) -1))) v_11233) (concat (mux (ugt v_11240 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11240 (mi (bitwidthMInt v_11240) -1))) v_11240) (concat (mux (ugt v_11247 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11247 (mi (bitwidthMInt v_11247) -1))) v_11247) (concat (mux (ugt v_11254 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11254 (mi (bitwidthMInt v_11254) -1))) v_11254) (mux (ugt v_11261 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11261 (mi (bitwidthMInt v_11261) -1))) v_11261))))))))))))))));
      pure ()
    pat_end
