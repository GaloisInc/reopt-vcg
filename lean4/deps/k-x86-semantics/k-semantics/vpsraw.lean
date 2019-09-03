def vpsraw1 : instruction :=
  definst "vpsraw" $ do
    pattern fun (v_3259 : imm int) (v_3261 : reg (bv 128)) (v_3262 : reg (bv 128)) => do
      v_8465 <- getRegister v_3261;
      v_8469 <- eval (handleImmediateWithSignExtend v_3259 8 8);
      v_8474 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8469) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8469)));
      setRegister (lhs.of_reg v_3262) (concat (ashr (mi 16 (svalueMInt (extract v_8465 0 16))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 16 32))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 32 48))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 48 64))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 64 80))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 80 96))) v_8474) (concat (ashr (mi 16 (svalueMInt (extract v_8465 96 112))) v_8474) (ashr (mi 16 (svalueMInt (extract v_8465 112 128))) v_8474))))))));
      pure ()
    pat_end;
    pattern fun (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) (v_3273 : reg (bv 128)) => do
      v_8517 <- getRegister v_3272;
      v_8521 <- getRegister v_3271;
      v_8526 <- eval (uvalueMInt (mux (ugt (extract v_8521 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8521 112 128)));
      setRegister (lhs.of_reg v_3273) (concat (ashr (mi 16 (svalueMInt (extract v_8517 0 16))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 16 32))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 32 48))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 48 64))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 64 80))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 80 96))) v_8526) (concat (ashr (mi 16 (svalueMInt (extract v_8517 96 112))) v_8526) (ashr (mi 16 (svalueMInt (extract v_8517 112 128))) v_8526))))))));
      pure ()
    pat_end;
    pattern fun (v_3276 : imm int) (v_3279 : reg (bv 256)) (v_3280 : reg (bv 256)) => do
      v_8564 <- getRegister v_3279;
      v_8568 <- eval (handleImmediateWithSignExtend v_3276 8 8);
      v_8573 <- eval (uvalueMInt (mux (ugt (concat (expression.bv_nat 56 0) v_8568) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_8568)));
      setRegister (lhs.of_reg v_3280) (concat (ashr (mi 16 (svalueMInt (extract v_8564 0 16))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 16 32))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 32 48))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 48 64))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 64 80))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 80 96))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 96 112))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 112 128))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 128 144))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 144 160))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 160 176))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 176 192))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 192 208))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 208 224))) v_8573) (concat (ashr (mi 16 (svalueMInt (extract v_8564 224 240))) v_8573) (ashr (mi 16 (svalueMInt (extract v_8564 240 256))) v_8573))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3288 : reg (bv 128)) (v_3290 : reg (bv 256)) (v_3291 : reg (bv 256)) => do
      v_8656 <- getRegister v_3290;
      v_8660 <- getRegister v_3288;
      v_8665 <- eval (uvalueMInt (mux (ugt (extract v_8660 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_8660 112 128)));
      setRegister (lhs.of_reg v_3291) (concat (ashr (mi 16 (svalueMInt (extract v_8656 0 16))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 16 32))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 32 48))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 48 64))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 64 80))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 80 96))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 96 112))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 112 128))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 128 144))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 144 160))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 160 176))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 176 192))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 192 208))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 208 224))) v_8665) (concat (ashr (mi 16 (svalueMInt (extract v_8656 224 240))) v_8665) (ashr (mi 16 (svalueMInt (extract v_8656 240 256))) v_8665))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3265 : Mem) (v_3266 : reg (bv 128)) (v_3267 : reg (bv 128)) => do
      v_14633 <- getRegister v_3266;
      v_14637 <- evaluateAddress v_3265;
      v_14638 <- load v_14637 16;
      v_14643 <- eval (uvalueMInt (mux (ugt (extract v_14638 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14638 112 128)));
      setRegister (lhs.of_reg v_3267) (concat (ashr (mi 16 (svalueMInt (extract v_14633 0 16))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 16 32))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 32 48))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 48 64))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 64 80))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 80 96))) v_14643) (concat (ashr (mi 16 (svalueMInt (extract v_14633 96 112))) v_14643) (ashr (mi 16 (svalueMInt (extract v_14633 112 128))) v_14643))))))));
      pure ()
    pat_end;
    pattern fun (v_3282 : Mem) (v_3284 : reg (bv 256)) (v_3285 : reg (bv 256)) => do
      v_14681 <- getRegister v_3284;
      v_14685 <- evaluateAddress v_3282;
      v_14686 <- load v_14685 16;
      v_14691 <- eval (uvalueMInt (mux (ugt (extract v_14686 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (extract v_14686 112 128)));
      setRegister (lhs.of_reg v_3285) (concat (ashr (mi 16 (svalueMInt (extract v_14681 0 16))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 16 32))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 32 48))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 48 64))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 64 80))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 80 96))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 96 112))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 112 128))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 128 144))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 144 160))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 160 176))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 176 192))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 192 208))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 208 224))) v_14691) (concat (ashr (mi 16 (svalueMInt (extract v_14681 224 240))) v_14691) (ashr (mi 16 (svalueMInt (extract v_14681 240 256))) v_14691))))))))))))))));
      pure ()
    pat_end
