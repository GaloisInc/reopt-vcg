def vphminposuw1 : instruction :=
  definst "vphminposuw" $ do
    pattern fun (v_3225 : reg (bv 128)) (v_3226 : reg (bv 128)) => do
      v_9257 <- getRegister v_3225;
      v_9258 <- eval (extract v_9257 0 16);
      v_9259 <- eval (extract v_9257 16 32);
      v_9260 <- eval (extract v_9257 32 48);
      v_9261 <- eval (extract v_9257 48 64);
      v_9262 <- eval (extract v_9257 64 80);
      v_9263 <- eval (extract v_9257 80 96);
      v_9264 <- eval (extract v_9257 96 112);
      v_9265 <- eval (extract v_9257 112 128);
      v_9266 <- eval (ult v_9264 v_9265);
      v_9267 <- eval (mux v_9266 v_9264 v_9265);
      v_9268 <- eval (ult v_9263 v_9267);
      v_9269 <- eval (mux v_9268 v_9263 v_9267);
      v_9270 <- eval (ult v_9262 v_9269);
      v_9271 <- eval (mux v_9270 v_9262 v_9269);
      v_9272 <- eval (ult v_9261 v_9271);
      v_9273 <- eval (mux v_9272 v_9261 v_9271);
      v_9274 <- eval (ult v_9260 v_9273);
      v_9275 <- eval (mux v_9274 v_9260 v_9273);
      v_9276 <- eval (ult v_9259 v_9275);
      v_9277 <- eval (mux v_9276 v_9259 v_9275);
      v_9278 <- eval (ult v_9258 v_9277);
      setRegister (lhs.of_reg v_3226) (concat (mux v_9278 (expression.bv_nat 112 7) (mux v_9276 (expression.bv_nat 112 6) (mux v_9274 (expression.bv_nat 112 5) (mux v_9272 (expression.bv_nat 112 4) (mux v_9270 (expression.bv_nat 112 3) (mux v_9268 (expression.bv_nat 112 2) (mux v_9266 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_9278 v_9258 v_9277));
      pure ()
    pat_end;
    pattern fun (v_3224 : Mem) (v_3221 : reg (bv 128)) => do
      v_17896 <- evaluateAddress v_3224;
      v_17897 <- load v_17896 16;
      v_17898 <- eval (extract v_17897 0 16);
      v_17899 <- eval (extract v_17897 16 32);
      v_17900 <- eval (extract v_17897 32 48);
      v_17901 <- eval (extract v_17897 48 64);
      v_17902 <- eval (extract v_17897 64 80);
      v_17903 <- eval (extract v_17897 80 96);
      v_17904 <- eval (extract v_17897 96 112);
      v_17905 <- eval (extract v_17897 112 128);
      v_17906 <- eval (ult v_17904 v_17905);
      v_17907 <- eval (mux v_17906 v_17904 v_17905);
      v_17908 <- eval (ult v_17903 v_17907);
      v_17909 <- eval (mux v_17908 v_17903 v_17907);
      v_17910 <- eval (ult v_17902 v_17909);
      v_17911 <- eval (mux v_17910 v_17902 v_17909);
      v_17912 <- eval (ult v_17901 v_17911);
      v_17913 <- eval (mux v_17912 v_17901 v_17911);
      v_17914 <- eval (ult v_17900 v_17913);
      v_17915 <- eval (mux v_17914 v_17900 v_17913);
      v_17916 <- eval (ult v_17899 v_17915);
      v_17917 <- eval (mux v_17916 v_17899 v_17915);
      v_17918 <- eval (ult v_17898 v_17917);
      setRegister (lhs.of_reg v_3221) (concat (mux v_17918 (expression.bv_nat 112 7) (mux v_17916 (expression.bv_nat 112 6) (mux v_17914 (expression.bv_nat 112 5) (mux v_17912 (expression.bv_nat 112 4) (mux v_17910 (expression.bv_nat 112 3) (mux v_17908 (expression.bv_nat 112 2) (mux v_17906 (expression.bv_nat 112 1) (expression.bv_nat 112 0)))))))) (mux v_17918 v_17898 v_17917));
      pure ()
    pat_end
