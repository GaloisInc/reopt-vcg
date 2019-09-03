def vpsllw1 : instruction :=
  definst "vpsllw" $ do
    pattern fun (v_3160 : imm int) (v_3158 : reg (bv 128)) (v_3159 : reg (bv 128)) => do
      v_8325 <- eval (handleImmediateWithSignExtend v_3160 8 8);
      v_8328 <- getRegister v_3158;
      v_8329 <- eval (extract v_8328 0 16);
      v_8331 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_8325));
      v_8335 <- eval (extract v_8328 16 32);
      v_8339 <- eval (extract v_8328 32 48);
      v_8343 <- eval (extract v_8328 48 64);
      v_8347 <- eval (extract v_8328 64 80);
      v_8351 <- eval (extract v_8328 80 96);
      v_8355 <- eval (extract v_8328 96 112);
      v_8359 <- eval (extract v_8328 112 128);
      setRegister (lhs.of_reg v_3159) (mux (ugt (concat (expression.bv_nat 56 0) v_8325) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_8329 v_8331) 0 (bitwidthMInt v_8329)) (concat (extract (shl v_8335 v_8331) 0 (bitwidthMInt v_8335)) (concat (extract (shl v_8339 v_8331) 0 (bitwidthMInt v_8339)) (concat (extract (shl v_8343 v_8331) 0 (bitwidthMInt v_8343)) (concat (extract (shl v_8347 v_8331) 0 (bitwidthMInt v_8347)) (concat (extract (shl v_8351 v_8331) 0 (bitwidthMInt v_8351)) (concat (extract (shl v_8355 v_8331) 0 (bitwidthMInt v_8355)) (extract (shl v_8359 v_8331) 0 (bitwidthMInt v_8359))))))))));
      pure ()
    pat_end;
    pattern fun (v_3169 : reg (bv 128)) (v_3170 : reg (bv 128)) (v_3171 : reg (bv 128)) => do
      v_8377 <- getRegister v_3169;
      v_8380 <- getRegister v_3170;
      v_8381 <- eval (extract v_8380 0 16);
      v_8383 <- eval (uvalueMInt (extract v_8377 112 128));
      v_8387 <- eval (extract v_8380 16 32);
      v_8391 <- eval (extract v_8380 32 48);
      v_8395 <- eval (extract v_8380 48 64);
      v_8399 <- eval (extract v_8380 64 80);
      v_8403 <- eval (extract v_8380 80 96);
      v_8407 <- eval (extract v_8380 96 112);
      v_8411 <- eval (extract v_8380 112 128);
      setRegister (lhs.of_reg v_3171) (mux (ugt (extract v_8377 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_8381 v_8383) 0 (bitwidthMInt v_8381)) (concat (extract (shl v_8387 v_8383) 0 (bitwidthMInt v_8387)) (concat (extract (shl v_8391 v_8383) 0 (bitwidthMInt v_8391)) (concat (extract (shl v_8395 v_8383) 0 (bitwidthMInt v_8395)) (concat (extract (shl v_8399 v_8383) 0 (bitwidthMInt v_8399)) (concat (extract (shl v_8403 v_8383) 0 (bitwidthMInt v_8403)) (concat (extract (shl v_8407 v_8383) 0 (bitwidthMInt v_8407)) (extract (shl v_8411 v_8383) 0 (bitwidthMInt v_8411))))))))));
      pure ()
    pat_end;
    pattern fun (v_3175 : imm int) (v_3176 : reg (bv 256)) (v_3177 : reg (bv 256)) => do
      v_8424 <- eval (handleImmediateWithSignExtend v_3175 8 8);
      v_8427 <- getRegister v_3176;
      v_8428 <- eval (extract v_8427 0 16);
      v_8430 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_8424));
      v_8434 <- eval (extract v_8427 16 32);
      v_8438 <- eval (extract v_8427 32 48);
      v_8442 <- eval (extract v_8427 48 64);
      v_8446 <- eval (extract v_8427 64 80);
      v_8450 <- eval (extract v_8427 80 96);
      v_8454 <- eval (extract v_8427 96 112);
      v_8458 <- eval (extract v_8427 112 128);
      v_8462 <- eval (extract v_8427 128 144);
      v_8466 <- eval (extract v_8427 144 160);
      v_8470 <- eval (extract v_8427 160 176);
      v_8474 <- eval (extract v_8427 176 192);
      v_8478 <- eval (extract v_8427 192 208);
      v_8482 <- eval (extract v_8427 208 224);
      v_8486 <- eval (extract v_8427 224 240);
      v_8490 <- eval (extract v_8427 240 256);
      setRegister (lhs.of_reg v_3177) (mux (ugt (concat (expression.bv_nat 56 0) v_8424) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl v_8428 v_8430) 0 (bitwidthMInt v_8428)) (concat (extract (shl v_8434 v_8430) 0 (bitwidthMInt v_8434)) (concat (extract (shl v_8438 v_8430) 0 (bitwidthMInt v_8438)) (concat (extract (shl v_8442 v_8430) 0 (bitwidthMInt v_8442)) (concat (extract (shl v_8446 v_8430) 0 (bitwidthMInt v_8446)) (concat (extract (shl v_8450 v_8430) 0 (bitwidthMInt v_8450)) (concat (extract (shl v_8454 v_8430) 0 (bitwidthMInt v_8454)) (concat (extract (shl v_8458 v_8430) 0 (bitwidthMInt v_8458)) (concat (extract (shl v_8462 v_8430) 0 (bitwidthMInt v_8462)) (concat (extract (shl v_8466 v_8430) 0 (bitwidthMInt v_8466)) (concat (extract (shl v_8470 v_8430) 0 (bitwidthMInt v_8470)) (concat (extract (shl v_8474 v_8430) 0 (bitwidthMInt v_8474)) (concat (extract (shl v_8478 v_8430) 0 (bitwidthMInt v_8478)) (concat (extract (shl v_8482 v_8430) 0 (bitwidthMInt v_8482)) (concat (extract (shl v_8486 v_8430) 0 (bitwidthMInt v_8486)) (extract (shl v_8490 v_8430) 0 (bitwidthMInt v_8490))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3186 : reg (bv 128)) (v_3187 : reg (bv 256)) (v_3188 : reg (bv 256)) => do
      v_8516 <- getRegister v_3186;
      v_8519 <- getRegister v_3187;
      v_8520 <- eval (extract v_8519 0 16);
      v_8522 <- eval (uvalueMInt (extract v_8516 112 128));
      v_8526 <- eval (extract v_8519 16 32);
      v_8530 <- eval (extract v_8519 32 48);
      v_8534 <- eval (extract v_8519 48 64);
      v_8538 <- eval (extract v_8519 64 80);
      v_8542 <- eval (extract v_8519 80 96);
      v_8546 <- eval (extract v_8519 96 112);
      v_8550 <- eval (extract v_8519 112 128);
      v_8554 <- eval (extract v_8519 128 144);
      v_8558 <- eval (extract v_8519 144 160);
      v_8562 <- eval (extract v_8519 160 176);
      v_8566 <- eval (extract v_8519 176 192);
      v_8570 <- eval (extract v_8519 192 208);
      v_8574 <- eval (extract v_8519 208 224);
      v_8578 <- eval (extract v_8519 224 240);
      v_8582 <- eval (extract v_8519 240 256);
      setRegister (lhs.of_reg v_3188) (mux (ugt (extract v_8516 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl v_8520 v_8522) 0 (bitwidthMInt v_8520)) (concat (extract (shl v_8526 v_8522) 0 (bitwidthMInt v_8526)) (concat (extract (shl v_8530 v_8522) 0 (bitwidthMInt v_8530)) (concat (extract (shl v_8534 v_8522) 0 (bitwidthMInt v_8534)) (concat (extract (shl v_8538 v_8522) 0 (bitwidthMInt v_8538)) (concat (extract (shl v_8542 v_8522) 0 (bitwidthMInt v_8542)) (concat (extract (shl v_8546 v_8522) 0 (bitwidthMInt v_8546)) (concat (extract (shl v_8550 v_8522) 0 (bitwidthMInt v_8550)) (concat (extract (shl v_8554 v_8522) 0 (bitwidthMInt v_8554)) (concat (extract (shl v_8558 v_8522) 0 (bitwidthMInt v_8558)) (concat (extract (shl v_8562 v_8522) 0 (bitwidthMInt v_8562)) (concat (extract (shl v_8566 v_8522) 0 (bitwidthMInt v_8566)) (concat (extract (shl v_8570 v_8522) 0 (bitwidthMInt v_8570)) (concat (extract (shl v_8574 v_8522) 0 (bitwidthMInt v_8574)) (concat (extract (shl v_8578 v_8522) 0 (bitwidthMInt v_8578)) (extract (shl v_8582 v_8522) 0 (bitwidthMInt v_8582))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3166 : Mem) (v_3164 : reg (bv 128)) (v_3165 : reg (bv 128)) => do
      v_15171 <- evaluateAddress v_3166;
      v_15172 <- load v_15171 16;
      v_15175 <- getRegister v_3164;
      v_15176 <- eval (extract v_15175 0 16);
      v_15178 <- eval (uvalueMInt (extract v_15172 112 128));
      v_15182 <- eval (extract v_15175 16 32);
      v_15186 <- eval (extract v_15175 32 48);
      v_15190 <- eval (extract v_15175 48 64);
      v_15194 <- eval (extract v_15175 64 80);
      v_15198 <- eval (extract v_15175 80 96);
      v_15202 <- eval (extract v_15175 96 112);
      v_15206 <- eval (extract v_15175 112 128);
      setRegister (lhs.of_reg v_3165) (mux (ugt (extract v_15172 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (extract (shl v_15176 v_15178) 0 (bitwidthMInt v_15176)) (concat (extract (shl v_15182 v_15178) 0 (bitwidthMInt v_15182)) (concat (extract (shl v_15186 v_15178) 0 (bitwidthMInt v_15186)) (concat (extract (shl v_15190 v_15178) 0 (bitwidthMInt v_15190)) (concat (extract (shl v_15194 v_15178) 0 (bitwidthMInt v_15194)) (concat (extract (shl v_15198 v_15178) 0 (bitwidthMInt v_15198)) (concat (extract (shl v_15202 v_15178) 0 (bitwidthMInt v_15202)) (extract (shl v_15206 v_15178) 0 (bitwidthMInt v_15206))))))))));
      pure ()
    pat_end;
    pattern fun (v_3181 : Mem) (v_3182 : reg (bv 256)) (v_3183 : reg (bv 256)) => do
      v_15219 <- evaluateAddress v_3181;
      v_15220 <- load v_15219 16;
      v_15223 <- getRegister v_3182;
      v_15224 <- eval (extract v_15223 0 16);
      v_15226 <- eval (uvalueMInt (extract v_15220 112 128));
      v_15230 <- eval (extract v_15223 16 32);
      v_15234 <- eval (extract v_15223 32 48);
      v_15238 <- eval (extract v_15223 48 64);
      v_15242 <- eval (extract v_15223 64 80);
      v_15246 <- eval (extract v_15223 80 96);
      v_15250 <- eval (extract v_15223 96 112);
      v_15254 <- eval (extract v_15223 112 128);
      v_15258 <- eval (extract v_15223 128 144);
      v_15262 <- eval (extract v_15223 144 160);
      v_15266 <- eval (extract v_15223 160 176);
      v_15270 <- eval (extract v_15223 176 192);
      v_15274 <- eval (extract v_15223 192 208);
      v_15278 <- eval (extract v_15223 208 224);
      v_15282 <- eval (extract v_15223 224 240);
      v_15286 <- eval (extract v_15223 240 256);
      setRegister (lhs.of_reg v_3183) (mux (ugt (extract v_15220 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (extract (shl v_15224 v_15226) 0 (bitwidthMInt v_15224)) (concat (extract (shl v_15230 v_15226) 0 (bitwidthMInt v_15230)) (concat (extract (shl v_15234 v_15226) 0 (bitwidthMInt v_15234)) (concat (extract (shl v_15238 v_15226) 0 (bitwidthMInt v_15238)) (concat (extract (shl v_15242 v_15226) 0 (bitwidthMInt v_15242)) (concat (extract (shl v_15246 v_15226) 0 (bitwidthMInt v_15246)) (concat (extract (shl v_15250 v_15226) 0 (bitwidthMInt v_15250)) (concat (extract (shl v_15254 v_15226) 0 (bitwidthMInt v_15254)) (concat (extract (shl v_15258 v_15226) 0 (bitwidthMInt v_15258)) (concat (extract (shl v_15262 v_15226) 0 (bitwidthMInt v_15262)) (concat (extract (shl v_15266 v_15226) 0 (bitwidthMInt v_15266)) (concat (extract (shl v_15270 v_15226) 0 (bitwidthMInt v_15270)) (concat (extract (shl v_15274 v_15226) 0 (bitwidthMInt v_15274)) (concat (extract (shl v_15278 v_15226) 0 (bitwidthMInt v_15278)) (concat (extract (shl v_15282 v_15226) 0 (bitwidthMInt v_15282)) (extract (shl v_15286 v_15226) 0 (bitwidthMInt v_15286))))))))))))))))));
      pure ()
    pat_end
