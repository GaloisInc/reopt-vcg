def psignb1 : instruction :=
  definst "psignb" $ do
    pattern fun (v_2946 : reg (bv 128)) (v_2947 : reg (bv 128)) => do
      v_7262 <- getRegister v_2946;
      v_7263 <- eval (extract v_7262 0 8);
      v_7265 <- getRegister v_2947;
      v_7266 <- eval (extract v_7265 0 8);
      v_7272 <- eval (extract v_7262 8 16);
      v_7274 <- eval (extract v_7265 8 16);
      v_7280 <- eval (extract v_7262 16 24);
      v_7282 <- eval (extract v_7265 16 24);
      v_7288 <- eval (extract v_7262 24 32);
      v_7290 <- eval (extract v_7265 24 32);
      v_7296 <- eval (extract v_7262 32 40);
      v_7298 <- eval (extract v_7265 32 40);
      v_7304 <- eval (extract v_7262 40 48);
      v_7306 <- eval (extract v_7265 40 48);
      v_7312 <- eval (extract v_7262 48 56);
      v_7314 <- eval (extract v_7265 48 56);
      v_7320 <- eval (extract v_7262 56 64);
      v_7322 <- eval (extract v_7265 56 64);
      v_7328 <- eval (extract v_7262 64 72);
      v_7330 <- eval (extract v_7265 64 72);
      v_7336 <- eval (extract v_7262 72 80);
      v_7338 <- eval (extract v_7265 72 80);
      v_7344 <- eval (extract v_7262 80 88);
      v_7346 <- eval (extract v_7265 80 88);
      v_7352 <- eval (extract v_7262 88 96);
      v_7354 <- eval (extract v_7265 88 96);
      v_7360 <- eval (extract v_7262 96 104);
      v_7362 <- eval (extract v_7265 96 104);
      v_7368 <- eval (extract v_7262 104 112);
      v_7370 <- eval (extract v_7265 104 112);
      v_7376 <- eval (extract v_7262 112 120);
      v_7378 <- eval (extract v_7265 112 120);
      v_7384 <- eval (extract v_7262 120 128);
      v_7386 <- eval (extract v_7265 120 128);
      setRegister (lhs.of_reg v_2947) (concat (mux (sgt v_7263 (expression.bv_nat 8 0)) v_7266 (mux (eq v_7263 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7266 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7272 (expression.bv_nat 8 0)) v_7274 (mux (eq v_7272 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7274 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7280 (expression.bv_nat 8 0)) v_7282 (mux (eq v_7280 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7282 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7288 (expression.bv_nat 8 0)) v_7290 (mux (eq v_7288 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7290 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7296 (expression.bv_nat 8 0)) v_7298 (mux (eq v_7296 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7298 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7304 (expression.bv_nat 8 0)) v_7306 (mux (eq v_7304 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7306 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7312 (expression.bv_nat 8 0)) v_7314 (mux (eq v_7312 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7314 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7320 (expression.bv_nat 8 0)) v_7322 (mux (eq v_7320 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7322 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7328 (expression.bv_nat 8 0)) v_7330 (mux (eq v_7328 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7330 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7336 (expression.bv_nat 8 0)) v_7338 (mux (eq v_7336 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7338 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7344 (expression.bv_nat 8 0)) v_7346 (mux (eq v_7344 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7346 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7352 (expression.bv_nat 8 0)) v_7354 (mux (eq v_7352 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7354 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7360 (expression.bv_nat 8 0)) v_7362 (mux (eq v_7360 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7362 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7368 (expression.bv_nat 8 0)) v_7370 (mux (eq v_7368 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7370 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7376 (expression.bv_nat 8 0)) v_7378 (mux (eq v_7376 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7378 (expression.bv_nat 8 255))))) (mux (sgt v_7384 (expression.bv_nat 8 0)) v_7386 (mux (eq v_7384 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7386 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2942 : Mem) (v_2943 : reg (bv 128)) => do
      v_14148 <- evaluateAddress v_2942;
      v_14149 <- load v_14148 16;
      v_14150 <- eval (extract v_14149 0 8);
      v_14152 <- getRegister v_2943;
      v_14153 <- eval (extract v_14152 0 8);
      v_14159 <- eval (extract v_14149 8 16);
      v_14161 <- eval (extract v_14152 8 16);
      v_14167 <- eval (extract v_14149 16 24);
      v_14169 <- eval (extract v_14152 16 24);
      v_14175 <- eval (extract v_14149 24 32);
      v_14177 <- eval (extract v_14152 24 32);
      v_14183 <- eval (extract v_14149 32 40);
      v_14185 <- eval (extract v_14152 32 40);
      v_14191 <- eval (extract v_14149 40 48);
      v_14193 <- eval (extract v_14152 40 48);
      v_14199 <- eval (extract v_14149 48 56);
      v_14201 <- eval (extract v_14152 48 56);
      v_14207 <- eval (extract v_14149 56 64);
      v_14209 <- eval (extract v_14152 56 64);
      v_14215 <- eval (extract v_14149 64 72);
      v_14217 <- eval (extract v_14152 64 72);
      v_14223 <- eval (extract v_14149 72 80);
      v_14225 <- eval (extract v_14152 72 80);
      v_14231 <- eval (extract v_14149 80 88);
      v_14233 <- eval (extract v_14152 80 88);
      v_14239 <- eval (extract v_14149 88 96);
      v_14241 <- eval (extract v_14152 88 96);
      v_14247 <- eval (extract v_14149 96 104);
      v_14249 <- eval (extract v_14152 96 104);
      v_14255 <- eval (extract v_14149 104 112);
      v_14257 <- eval (extract v_14152 104 112);
      v_14263 <- eval (extract v_14149 112 120);
      v_14265 <- eval (extract v_14152 112 120);
      v_14271 <- eval (extract v_14149 120 128);
      v_14273 <- eval (extract v_14152 120 128);
      setRegister (lhs.of_reg v_2943) (concat (mux (sgt v_14150 (expression.bv_nat 8 0)) v_14153 (mux (eq v_14150 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14153 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14159 (expression.bv_nat 8 0)) v_14161 (mux (eq v_14159 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14161 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14167 (expression.bv_nat 8 0)) v_14169 (mux (eq v_14167 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14169 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14175 (expression.bv_nat 8 0)) v_14177 (mux (eq v_14175 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14177 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14183 (expression.bv_nat 8 0)) v_14185 (mux (eq v_14183 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14185 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14191 (expression.bv_nat 8 0)) v_14193 (mux (eq v_14191 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14193 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14199 (expression.bv_nat 8 0)) v_14201 (mux (eq v_14199 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14201 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14207 (expression.bv_nat 8 0)) v_14209 (mux (eq v_14207 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14209 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14215 (expression.bv_nat 8 0)) v_14217 (mux (eq v_14215 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14217 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14223 (expression.bv_nat 8 0)) v_14225 (mux (eq v_14223 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14225 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14231 (expression.bv_nat 8 0)) v_14233 (mux (eq v_14231 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14233 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14239 (expression.bv_nat 8 0)) v_14241 (mux (eq v_14239 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14241 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14247 (expression.bv_nat 8 0)) v_14249 (mux (eq v_14247 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14249 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14255 (expression.bv_nat 8 0)) v_14257 (mux (eq v_14255 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14257 (expression.bv_nat 8 255))))) (concat (mux (sgt v_14263 (expression.bv_nat 8 0)) v_14265 (mux (eq v_14263 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14265 (expression.bv_nat 8 255))))) (mux (sgt v_14271 (expression.bv_nat 8 0)) v_14273 (mux (eq v_14271 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14273 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
