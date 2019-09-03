def vpsrad1 : instruction :=
  definst "vpsrad" $ do
    pattern fun (v_3203 : imm int) (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_8209 <- getRegister v_3205;
      v_8213 <- eval (handleImmediateWithSignExtend v_3203 8 8);
      v_8218 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8213) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8213)));
      setRegister (lhs.of_reg v_3206) (concat (ashr (mi 32 (svalueMInt (extract v_8209 0 32))) v_8218) (concat (ashr (mi 32 (svalueMInt (extract v_8209 32 64))) v_8218) (concat (ashr (mi 32 (svalueMInt (extract v_8209 64 96))) v_8218) (ashr (mi 32 (svalueMInt (extract v_8209 96 128))) v_8218))));
      pure ()
    pat_end;
    pattern fun (v_3215 : reg (bv 128)) (v_3216 : reg (bv 128)) (v_3217 : reg (bv 128)) => do
      v_8241 <- getRegister v_3216;
      v_8245 <- getRegister v_3215;
      v_8250 <- eval (uvalueMInt (mux (ugt (extract v_8245 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8245 96 128)));
      setRegister (lhs.of_reg v_3217) (concat (ashr (mi 32 (svalueMInt (extract v_8241 0 32))) v_8250) (concat (ashr (mi 32 (svalueMInt (extract v_8241 32 64))) v_8250) (concat (ashr (mi 32 (svalueMInt (extract v_8241 64 96))) v_8250) (ashr (mi 32 (svalueMInt (extract v_8241 96 128))) v_8250))));
      pure ()
    pat_end;
    pattern fun (v_3220 : imm int) (v_3223 : reg (bv 256)) (v_3224 : reg (bv 256)) => do
      v_8268 <- getRegister v_3223;
      v_8272 <- eval (handleImmediateWithSignExtend v_3220 8 8);
      v_8277 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8272) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_8272)));
      setRegister (lhs.of_reg v_3224) (concat (ashr (mi 32 (svalueMInt (extract v_8268 0 32))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 32 64))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 64 96))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 96 128))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 128 160))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 160 192))) v_8277) (concat (ashr (mi 32 (svalueMInt (extract v_8268 192 224))) v_8277) (ashr (mi 32 (svalueMInt (extract v_8268 224 256))) v_8277))))))));
      pure ()
    pat_end;
    pattern fun (v_3232 : reg (bv 128)) (v_3234 : reg (bv 256)) (v_3235 : reg (bv 256)) => do
      v_8320 <- getRegister v_3234;
      v_8324 <- getRegister v_3232;
      v_8329 <- eval (uvalueMInt (mux (ugt (extract v_8324 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_8324 96 128)));
      setRegister (lhs.of_reg v_3235) (concat (ashr (mi 32 (svalueMInt (extract v_8320 0 32))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 32 64))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 64 96))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 96 128))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 128 160))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 160 192))) v_8329) (concat (ashr (mi 32 (svalueMInt (extract v_8320 192 224))) v_8329) (ashr (mi 32 (svalueMInt (extract v_8320 224 256))) v_8329))))))));
      pure ()
    pat_end;
    pattern fun (v_3209 : Mem) (v_3210 : reg (bv 128)) (v_3211 : reg (bv 128)) => do
      v_14467 <- getRegister v_3210;
      v_14471 <- evaluateAddress v_3209;
      v_14472 <- load v_14471 16;
      v_14477 <- eval (uvalueMInt (mux (ugt (extract v_14472 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14472 96 128)));
      setRegister (lhs.of_reg v_3211) (concat (ashr (mi 32 (svalueMInt (extract v_14467 0 32))) v_14477) (concat (ashr (mi 32 (svalueMInt (extract v_14467 32 64))) v_14477) (concat (ashr (mi 32 (svalueMInt (extract v_14467 64 96))) v_14477) (ashr (mi 32 (svalueMInt (extract v_14467 96 128))) v_14477))));
      pure ()
    pat_end;
    pattern fun (v_3226 : Mem) (v_3228 : reg (bv 256)) (v_3229 : reg (bv 256)) => do
      v_14495 <- getRegister v_3228;
      v_14499 <- evaluateAddress v_3226;
      v_14500 <- load v_14499 16;
      v_14505 <- eval (uvalueMInt (mux (ugt (extract v_14500 64 128) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (extract v_14500 96 128)));
      setRegister (lhs.of_reg v_3229) (concat (ashr (mi 32 (svalueMInt (extract v_14495 0 32))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 32 64))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 64 96))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 96 128))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 128 160))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 160 192))) v_14505) (concat (ashr (mi 32 (svalueMInt (extract v_14495 192 224))) v_14505) (ashr (mi 32 (svalueMInt (extract v_14495 224 256))) v_14505))))))));
      pure ()
    pat_end
