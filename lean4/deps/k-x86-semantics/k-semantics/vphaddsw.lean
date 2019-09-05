def vphaddsw1 : instruction :=
  definst "vphaddsw" $ do
    pattern fun (v_3236 : reg (bv 128)) (v_3237 : reg (bv 128)) (v_3238 : reg (bv 128)) => do
      v_8725 <- getRegister v_3236;
      v_8730 <- eval (add (sext (extract v_8725 0 16) 32) (sext (extract v_8725 16 32) 32));
      v_8740 <- eval (add (sext (extract v_8725 32 48) 32) (sext (extract v_8725 48 64) 32));
      v_8750 <- eval (add (sext (extract v_8725 64 80) 32) (sext (extract v_8725 80 96) 32));
      v_8760 <- eval (add (sext (extract v_8725 96 112) 32) (sext (extract v_8725 112 128) 32));
      v_8766 <- getRegister v_3237;
      v_8771 <- eval (add (sext (extract v_8766 0 16) 32) (sext (extract v_8766 16 32) 32));
      v_8781 <- eval (add (sext (extract v_8766 32 48) 32) (sext (extract v_8766 48 64) 32));
      v_8791 <- eval (add (sext (extract v_8766 64 80) 32) (sext (extract v_8766 80 96) 32));
      v_8801 <- eval (add (sext (extract v_8766 112 128) 32) (sext (extract v_8766 96 112) 32));
      setRegister (lhs.of_reg v_3238) (concat (mux (sgt v_8730 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8730 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8730 16 32))) (concat (mux (sgt v_8740 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8740 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8740 16 32))) (concat (mux (sgt v_8750 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8750 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8750 16 32))) (concat (mux (sgt v_8760 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8760 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8760 16 32))) (concat (mux (sgt v_8771 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8771 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8771 16 32))) (concat (mux (sgt v_8781 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8781 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8781 16 32))) (concat (mux (sgt v_8791 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8791 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8791 16 32))) (mux (sgt v_8801 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8801 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8801 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3246 : reg (bv 256)) (v_3247 : reg (bv 256)) (v_3248 : reg (bv 256)) => do
      v_8820 <- getRegister v_3246;
      v_8825 <- eval (add (sext (extract v_8820 0 16) 32) (sext (extract v_8820 16 32) 32));
      v_8835 <- eval (add (sext (extract v_8820 32 48) 32) (sext (extract v_8820 48 64) 32));
      v_8845 <- eval (add (sext (extract v_8820 64 80) 32) (sext (extract v_8820 80 96) 32));
      v_8855 <- eval (add (sext (extract v_8820 96 112) 32) (sext (extract v_8820 112 128) 32));
      v_8861 <- getRegister v_3247;
      v_8866 <- eval (add (sext (extract v_8861 0 16) 32) (sext (extract v_8861 16 32) 32));
      v_8876 <- eval (add (sext (extract v_8861 32 48) 32) (sext (extract v_8861 48 64) 32));
      v_8886 <- eval (add (sext (extract v_8861 64 80) 32) (sext (extract v_8861 80 96) 32));
      v_8896 <- eval (add (sext (extract v_8861 96 112) 32) (sext (extract v_8861 112 128) 32));
      v_8906 <- eval (add (sext (extract v_8820 128 144) 32) (sext (extract v_8820 144 160) 32));
      v_8916 <- eval (add (sext (extract v_8820 160 176) 32) (sext (extract v_8820 176 192) 32));
      v_8926 <- eval (add (sext (extract v_8820 192 208) 32) (sext (extract v_8820 208 224) 32));
      v_8936 <- eval (add (sext (extract v_8820 224 240) 32) (sext (extract v_8820 240 256) 32));
      v_8946 <- eval (add (sext (extract v_8861 128 144) 32) (sext (extract v_8861 144 160) 32));
      v_8956 <- eval (add (sext (extract v_8861 160 176) 32) (sext (extract v_8861 176 192) 32));
      v_8966 <- eval (add (sext (extract v_8861 192 208) 32) (sext (extract v_8861 208 224) 32));
      v_8976 <- eval (add (sext (extract v_8861 240 256) 32) (sext (extract v_8861 224 240) 32));
      setRegister (lhs.of_reg v_3248) (concat (mux (sgt v_8825 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8825 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8825 16 32))) (concat (mux (sgt v_8835 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8835 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8835 16 32))) (concat (mux (sgt v_8845 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8845 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8845 16 32))) (concat (mux (sgt v_8855 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8855 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8855 16 32))) (concat (mux (sgt v_8866 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8866 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8866 16 32))) (concat (mux (sgt v_8876 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8876 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8876 16 32))) (concat (mux (sgt v_8886 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8886 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8886 16 32))) (concat (mux (sgt v_8896 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8896 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8896 16 32))) (concat (mux (sgt v_8906 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8906 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8906 16 32))) (concat (mux (sgt v_8916 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8916 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8916 16 32))) (concat (mux (sgt v_8926 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8926 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8926 16 32))) (concat (mux (sgt v_8936 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8936 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8936 16 32))) (concat (mux (sgt v_8946 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8946 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8946 16 32))) (concat (mux (sgt v_8956 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8956 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8956 16 32))) (concat (mux (sgt v_8966 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8966 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8966 16 32))) (mux (sgt v_8976 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8976 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8976 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3230 : Mem) (v_3231 : reg (bv 128)) (v_3232 : reg (bv 128)) => do
      v_17137 <- evaluateAddress v_3230;
      v_17138 <- load v_17137 16;
      v_17143 <- eval (add (sext (extract v_17138 0 16) 32) (sext (extract v_17138 16 32) 32));
      v_17153 <- eval (add (sext (extract v_17138 32 48) 32) (sext (extract v_17138 48 64) 32));
      v_17163 <- eval (add (sext (extract v_17138 64 80) 32) (sext (extract v_17138 80 96) 32));
      v_17173 <- eval (add (sext (extract v_17138 96 112) 32) (sext (extract v_17138 112 128) 32));
      v_17179 <- getRegister v_3231;
      v_17184 <- eval (add (sext (extract v_17179 0 16) 32) (sext (extract v_17179 16 32) 32));
      v_17194 <- eval (add (sext (extract v_17179 32 48) 32) (sext (extract v_17179 48 64) 32));
      v_17204 <- eval (add (sext (extract v_17179 64 80) 32) (sext (extract v_17179 80 96) 32));
      v_17214 <- eval (add (sext (extract v_17179 112 128) 32) (sext (extract v_17179 96 112) 32));
      setRegister (lhs.of_reg v_3232) (concat (mux (sgt v_17143 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17143 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17143 16 32))) (concat (mux (sgt v_17153 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17153 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17153 16 32))) (concat (mux (sgt v_17163 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17163 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17163 16 32))) (concat (mux (sgt v_17173 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17173 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17173 16 32))) (concat (mux (sgt v_17184 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17184 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17184 16 32))) (concat (mux (sgt v_17194 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17194 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17194 16 32))) (concat (mux (sgt v_17204 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17204 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17204 16 32))) (mux (sgt v_17214 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17214 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17214 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_3241 : Mem) (v_3242 : reg (bv 256)) (v_3243 : reg (bv 256)) => do
      v_17228 <- evaluateAddress v_3241;
      v_17229 <- load v_17228 32;
      v_17234 <- eval (add (sext (extract v_17229 0 16) 32) (sext (extract v_17229 16 32) 32));
      v_17244 <- eval (add (sext (extract v_17229 32 48) 32) (sext (extract v_17229 48 64) 32));
      v_17254 <- eval (add (sext (extract v_17229 64 80) 32) (sext (extract v_17229 80 96) 32));
      v_17264 <- eval (add (sext (extract v_17229 96 112) 32) (sext (extract v_17229 112 128) 32));
      v_17270 <- getRegister v_3242;
      v_17275 <- eval (add (sext (extract v_17270 0 16) 32) (sext (extract v_17270 16 32) 32));
      v_17285 <- eval (add (sext (extract v_17270 32 48) 32) (sext (extract v_17270 48 64) 32));
      v_17295 <- eval (add (sext (extract v_17270 64 80) 32) (sext (extract v_17270 80 96) 32));
      v_17305 <- eval (add (sext (extract v_17270 96 112) 32) (sext (extract v_17270 112 128) 32));
      v_17315 <- eval (add (sext (extract v_17229 128 144) 32) (sext (extract v_17229 144 160) 32));
      v_17325 <- eval (add (sext (extract v_17229 160 176) 32) (sext (extract v_17229 176 192) 32));
      v_17335 <- eval (add (sext (extract v_17229 192 208) 32) (sext (extract v_17229 208 224) 32));
      v_17345 <- eval (add (sext (extract v_17229 224 240) 32) (sext (extract v_17229 240 256) 32));
      v_17355 <- eval (add (sext (extract v_17270 128 144) 32) (sext (extract v_17270 144 160) 32));
      v_17365 <- eval (add (sext (extract v_17270 160 176) 32) (sext (extract v_17270 176 192) 32));
      v_17375 <- eval (add (sext (extract v_17270 192 208) 32) (sext (extract v_17270 208 224) 32));
      v_17385 <- eval (add (sext (extract v_17270 240 256) 32) (sext (extract v_17270 224 240) 32));
      setRegister (lhs.of_reg v_3243) (concat (mux (sgt v_17234 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17234 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17234 16 32))) (concat (mux (sgt v_17244 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17244 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17244 16 32))) (concat (mux (sgt v_17254 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17254 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17254 16 32))) (concat (mux (sgt v_17264 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17264 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17264 16 32))) (concat (mux (sgt v_17275 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17275 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17275 16 32))) (concat (mux (sgt v_17285 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17285 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17285 16 32))) (concat (mux (sgt v_17295 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17295 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17295 16 32))) (concat (mux (sgt v_17305 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17305 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17305 16 32))) (concat (mux (sgt v_17315 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17315 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17315 16 32))) (concat (mux (sgt v_17325 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17325 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17325 16 32))) (concat (mux (sgt v_17335 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17335 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17335 16 32))) (concat (mux (sgt v_17345 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17345 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17345 16 32))) (concat (mux (sgt v_17355 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17355 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17355 16 32))) (concat (mux (sgt v_17365 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17365 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17365 16 32))) (concat (mux (sgt v_17375 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17375 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17375 16 32))) (mux (sgt v_17385 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17385 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17385 16 32))))))))))))))))));
      pure ()
    pat_end
