def vpackssdw1 : instruction :=
  definst "vpackssdw" $ do
    pattern fun (v_3297 : reg (bv 128)) (v_3298 : reg (bv 128)) (v_3299 : reg (bv 128)) => do
      v_5910 <- getRegister v_3297;
      v_5911 <- eval (extract v_5910 0 32);
      v_5917 <- eval (extract v_5910 32 64);
      v_5923 <- eval (extract v_5910 64 96);
      v_5929 <- eval (extract v_5910 96 128);
      v_5935 <- getRegister v_3298;
      v_5936 <- eval (extract v_5935 0 32);
      v_5942 <- eval (extract v_5935 32 64);
      v_5948 <- eval (extract v_5935 64 96);
      v_5954 <- eval (extract v_5935 96 128);
      setRegister (lhs.of_reg v_3299) (concat (mux (sgt v_5911 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5911 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5910 16 32))) (concat (mux (sgt v_5917 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5917 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5910 48 64))) (concat (mux (sgt v_5923 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5923 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5910 80 96))) (concat (mux (sgt v_5929 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5929 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5910 112 128))) (concat (mux (sgt v_5936 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5936 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5935 16 32))) (concat (mux (sgt v_5942 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5942 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5935 48 64))) (concat (mux (sgt v_5948 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5948 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5935 80 96))) (mux (sgt v_5954 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5954 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5935 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3309 : reg (bv 256)) (v_3310 : reg (bv 256)) (v_3311 : reg (bv 256)) => do
      v_5973 <- getRegister v_3309;
      v_5974 <- eval (extract v_5973 0 32);
      v_5980 <- eval (extract v_5973 32 64);
      v_5986 <- eval (extract v_5973 64 96);
      v_5992 <- eval (extract v_5973 96 128);
      v_5998 <- getRegister v_3310;
      v_5999 <- eval (extract v_5998 0 32);
      v_6005 <- eval (extract v_5998 32 64);
      v_6011 <- eval (extract v_5998 64 96);
      v_6017 <- eval (extract v_5998 96 128);
      v_6023 <- eval (extract v_5973 128 160);
      v_6029 <- eval (extract v_5973 160 192);
      v_6035 <- eval (extract v_5973 192 224);
      v_6041 <- eval (extract v_5973 224 256);
      v_6047 <- eval (extract v_5998 128 160);
      v_6053 <- eval (extract v_5998 160 192);
      v_6059 <- eval (extract v_5998 192 224);
      v_6065 <- eval (extract v_5998 224 256);
      setRegister (lhs.of_reg v_3311) (concat (mux (sgt v_5974 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5974 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 16 32))) (concat (mux (sgt v_5980 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5980 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 48 64))) (concat (mux (sgt v_5986 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5986 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 80 96))) (concat (mux (sgt v_5992 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5992 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 112 128))) (concat (mux (sgt v_5999 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5999 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 16 32))) (concat (mux (sgt v_6005 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6005 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 48 64))) (concat (mux (sgt v_6011 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6011 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 80 96))) (concat (mux (sgt v_6017 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6017 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 112 128))) (concat (mux (sgt v_6023 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6023 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 144 160))) (concat (mux (sgt v_6029 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6029 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 176 192))) (concat (mux (sgt v_6035 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6035 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 208 224))) (concat (mux (sgt v_6041 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6041 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5973 240 256))) (concat (mux (sgt v_6047 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6047 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 144 160))) (concat (mux (sgt v_6053 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6053 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 176 192))) (concat (mux (sgt v_6059 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6059 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 208 224))) (mux (sgt v_6065 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6065 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5998 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3292 : Mem) (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) => do
      v_10982 <- evaluateAddress v_3292;
      v_10983 <- load v_10982 16;
      v_10984 <- eval (extract v_10983 0 32);
      v_10990 <- eval (extract v_10983 32 64);
      v_10996 <- eval (extract v_10983 64 96);
      v_11002 <- eval (extract v_10983 96 128);
      v_11008 <- getRegister v_3293;
      v_11009 <- eval (extract v_11008 0 32);
      v_11015 <- eval (extract v_11008 32 64);
      v_11021 <- eval (extract v_11008 64 96);
      v_11027 <- eval (extract v_11008 96 128);
      setRegister (lhs.of_reg v_3294) (concat (mux (sgt v_10984 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10984 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10983 16 32))) (concat (mux (sgt v_10990 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10990 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10983 48 64))) (concat (mux (sgt v_10996 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10996 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10983 80 96))) (concat (mux (sgt v_11002 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11002 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10983 112 128))) (concat (mux (sgt v_11009 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11009 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11008 16 32))) (concat (mux (sgt v_11015 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11015 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11008 48 64))) (concat (mux (sgt v_11021 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11021 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11008 80 96))) (mux (sgt v_11027 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11027 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11008 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3304 : reg (bv 256)) (v_3305 : reg (bv 256)) => do
      v_11041 <- evaluateAddress v_3303;
      v_11042 <- load v_11041 32;
      v_11043 <- eval (extract v_11042 0 32);
      v_11049 <- eval (extract v_11042 32 64);
      v_11055 <- eval (extract v_11042 64 96);
      v_11061 <- eval (extract v_11042 96 128);
      v_11067 <- getRegister v_3304;
      v_11068 <- eval (extract v_11067 0 32);
      v_11074 <- eval (extract v_11067 32 64);
      v_11080 <- eval (extract v_11067 64 96);
      v_11086 <- eval (extract v_11067 96 128);
      v_11092 <- eval (extract v_11042 128 160);
      v_11098 <- eval (extract v_11042 160 192);
      v_11104 <- eval (extract v_11042 192 224);
      v_11110 <- eval (extract v_11042 224 256);
      v_11116 <- eval (extract v_11067 128 160);
      v_11122 <- eval (extract v_11067 160 192);
      v_11128 <- eval (extract v_11067 192 224);
      v_11134 <- eval (extract v_11067 224 256);
      setRegister (lhs.of_reg v_3305) (concat (mux (sgt v_11043 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11043 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 16 32))) (concat (mux (sgt v_11049 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11049 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 48 64))) (concat (mux (sgt v_11055 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11055 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 80 96))) (concat (mux (sgt v_11061 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11061 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 112 128))) (concat (mux (sgt v_11068 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11068 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 16 32))) (concat (mux (sgt v_11074 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11074 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 48 64))) (concat (mux (sgt v_11080 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11080 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 80 96))) (concat (mux (sgt v_11086 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11086 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 112 128))) (concat (mux (sgt v_11092 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11092 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 144 160))) (concat (mux (sgt v_11098 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11098 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 176 192))) (concat (mux (sgt v_11104 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11104 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 208 224))) (concat (mux (sgt v_11110 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11110 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11042 240 256))) (concat (mux (sgt v_11116 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11116 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 144 160))) (concat (mux (sgt v_11122 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11122 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 176 192))) (concat (mux (sgt v_11128 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11128 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 208 224))) (mux (sgt v_11134 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11134 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11067 240 256))))))))))))))))));
      pure ()
    pat_end
