def vpsrlw1 : instruction :=
  definst "vpsrlw" $ do
    pattern fun (v_3408 : imm int) (v_3406 : reg (bv 128)) (v_3407 : reg (bv 128)) => do
      v_9545 <- eval (handleImmediateWithSignExtend v_3408 8 8);
      v_9548 <- getRegister v_3406;
      v_9551 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_9545));
      setRegister (lhs.of_reg v_3407) (mux (ugt (concat (expression.bv_nat 56 0) v_9545) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_9548 0 16) v_9551) (concat (lshr (extract v_9548 16 32) v_9551) (concat (lshr (extract v_9548 32 48) v_9551) (concat (lshr (extract v_9548 48 64) v_9551) (concat (lshr (extract v_9548 64 80) v_9551) (concat (lshr (extract v_9548 80 96) v_9551) (concat (lshr (extract v_9548 96 112) v_9551) (lshr (extract v_9548 112 128) v_9551)))))))));
      pure ()
    pat_end;
    pattern fun (v_3417 : reg (bv 128)) (v_3418 : reg (bv 128)) (v_3419 : reg (bv 128)) => do
      v_9581 <- getRegister v_3417;
      v_9584 <- getRegister v_3418;
      v_9587 <- eval (uvalueMInt (extract v_9581 112 128));
      setRegister (lhs.of_reg v_3419) (mux (ugt (extract v_9581 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_9584 0 16) v_9587) (concat (lshr (extract v_9584 16 32) v_9587) (concat (lshr (extract v_9584 32 48) v_9587) (concat (lshr (extract v_9584 48 64) v_9587) (concat (lshr (extract v_9584 64 80) v_9587) (concat (lshr (extract v_9584 80 96) v_9587) (concat (lshr (extract v_9584 96 112) v_9587) (lshr (extract v_9584 112 128) v_9587)))))))));
      pure ()
    pat_end;
    pattern fun (v_3423 : imm int) (v_3424 : reg (bv 256)) (v_3425 : reg (bv 256)) => do
      v_9612 <- eval (handleImmediateWithSignExtend v_3423 8 8);
      v_9615 <- getRegister v_3424;
      v_9618 <- eval (uvalueMInt (concat (expression.bv_nat 8 0) v_9612));
      setRegister (lhs.of_reg v_3425) (mux (ugt (concat (expression.bv_nat 56 0) v_9612) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_9615 0 16) v_9618) (concat (lshr (extract v_9615 16 32) v_9618) (concat (lshr (extract v_9615 32 48) v_9618) (concat (lshr (extract v_9615 48 64) v_9618) (concat (lshr (extract v_9615 64 80) v_9618) (concat (lshr (extract v_9615 80 96) v_9618) (concat (lshr (extract v_9615 96 112) v_9618) (concat (lshr (extract v_9615 112 128) v_9618) (concat (lshr (extract v_9615 128 144) v_9618) (concat (lshr (extract v_9615 144 160) v_9618) (concat (lshr (extract v_9615 160 176) v_9618) (concat (lshr (extract v_9615 176 192) v_9618) (concat (lshr (extract v_9615 192 208) v_9618) (concat (lshr (extract v_9615 208 224) v_9618) (concat (lshr (extract v_9615 224 240) v_9618) (lshr (extract v_9615 240 256) v_9618)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3434 : reg (bv 128)) (v_3435 : reg (bv 256)) (v_3436 : reg (bv 256)) => do
      v_9672 <- getRegister v_3434;
      v_9675 <- getRegister v_3435;
      v_9678 <- eval (uvalueMInt (extract v_9672 112 128));
      setRegister (lhs.of_reg v_3436) (mux (ugt (extract v_9672 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_9675 0 16) v_9678) (concat (lshr (extract v_9675 16 32) v_9678) (concat (lshr (extract v_9675 32 48) v_9678) (concat (lshr (extract v_9675 48 64) v_9678) (concat (lshr (extract v_9675 64 80) v_9678) (concat (lshr (extract v_9675 80 96) v_9678) (concat (lshr (extract v_9675 96 112) v_9678) (concat (lshr (extract v_9675 112 128) v_9678) (concat (lshr (extract v_9675 128 144) v_9678) (concat (lshr (extract v_9675 144 160) v_9678) (concat (lshr (extract v_9675 160 176) v_9678) (concat (lshr (extract v_9675 176 192) v_9678) (concat (lshr (extract v_9675 192 208) v_9678) (concat (lshr (extract v_9675 208 224) v_9678) (concat (lshr (extract v_9675 224 240) v_9678) (lshr (extract v_9675 240 256) v_9678)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3414 : Mem) (v_3412 : reg (bv 128)) (v_3413 : reg (bv 128)) => do
      v_15843 <- evaluateAddress v_3414;
      v_15844 <- load v_15843 16;
      v_15847 <- getRegister v_3412;
      v_15850 <- eval (uvalueMInt (extract v_15844 112 128));
      setRegister (lhs.of_reg v_3413) (mux (ugt (extract v_15844 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 128 0) (concat (lshr (extract v_15847 0 16) v_15850) (concat (lshr (extract v_15847 16 32) v_15850) (concat (lshr (extract v_15847 32 48) v_15850) (concat (lshr (extract v_15847 48 64) v_15850) (concat (lshr (extract v_15847 64 80) v_15850) (concat (lshr (extract v_15847 80 96) v_15850) (concat (lshr (extract v_15847 96 112) v_15850) (lshr (extract v_15847 112 128) v_15850)))))))));
      pure ()
    pat_end;
    pattern fun (v_3429 : Mem) (v_3430 : reg (bv 256)) (v_3431 : reg (bv 256)) => do
      v_15875 <- evaluateAddress v_3429;
      v_15876 <- load v_15875 16;
      v_15879 <- getRegister v_3430;
      v_15882 <- eval (uvalueMInt (extract v_15876 112 128));
      setRegister (lhs.of_reg v_3431) (mux (ugt (extract v_15876 64 128) (expression.bv_nat 64 15)) (expression.bv_nat 256 0) (concat (lshr (extract v_15879 0 16) v_15882) (concat (lshr (extract v_15879 16 32) v_15882) (concat (lshr (extract v_15879 32 48) v_15882) (concat (lshr (extract v_15879 48 64) v_15882) (concat (lshr (extract v_15879 64 80) v_15882) (concat (lshr (extract v_15879 80 96) v_15882) (concat (lshr (extract v_15879 96 112) v_15882) (concat (lshr (extract v_15879 112 128) v_15882) (concat (lshr (extract v_15879 128 144) v_15882) (concat (lshr (extract v_15879 144 160) v_15882) (concat (lshr (extract v_15879 160 176) v_15882) (concat (lshr (extract v_15879 176 192) v_15882) (concat (lshr (extract v_15879 192 208) v_15882) (concat (lshr (extract v_15879 208 224) v_15882) (concat (lshr (extract v_15879 224 240) v_15882) (lshr (extract v_15879 240 256) v_15882)))))))))))))))));
      pure ()
    pat_end
