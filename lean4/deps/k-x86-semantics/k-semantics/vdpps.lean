def vdpps1 : instruction :=
  definst "vdpps" $ do
    pattern fun (v_3490 : imm int) (v_3492 : reg (bv 128)) (v_3493 : reg (bv 128)) (v_3494 : reg (bv 128)) => do
      v_6571 <- eval (handleImmediateWithSignExtend v_3490 8 8);
      v_6574 <- getRegister v_3493;
      v_6577 <- getRegister v_3492;
      v_6618 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6571 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6574 96 128) 24 8) (MInt2Float (extract v_6577 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_6571 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6574 64 96) 24 8) (MInt2Float (extract v_6577 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6571 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6574 32 64) 24 8) (MInt2Float (extract v_6577 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_6571 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6574 0 32) 24 8) (MInt2Float (extract v_6577 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3494) (concat (concat (concat (mux (isBitSet v_6571 4) v_6618 (expression.bv_nat 32 0)) (mux (isBitSet v_6571 5) v_6618 (expression.bv_nat 32 0))) (mux (isBitSet v_6571 6) v_6618 (expression.bv_nat 32 0))) (mux (isBitSet v_6571 7) v_6618 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3503 : imm int) (v_3504 : reg (bv 256)) (v_3505 : reg (bv 256)) (v_3506 : reg (bv 256)) => do
      v_6636 <- eval (handleImmediateWithSignExtend v_3503 8 8);
      v_6637 <- eval (isBitSet v_6636 4);
      v_6638 <- eval (isBitSet v_6636 3);
      v_6639 <- getRegister v_3505;
      v_6642 <- getRegister v_3504;
      v_6649 <- eval (isBitSet v_6636 2);
      v_6661 <- eval (isBitSet v_6636 1);
      v_6670 <- eval (isBitSet v_6636 0);
      v_6683 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6638 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 96 128) 24 8) (MInt2Float (extract v_6642 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6649 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 64 96) 24 8) (MInt2Float (extract v_6642 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6661 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 32 64) 24 8) (MInt2Float (extract v_6642 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6670 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 0 32) 24 8) (MInt2Float (extract v_6642 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_6685 <- eval (isBitSet v_6636 5);
      v_6688 <- eval (isBitSet v_6636 6);
      v_6691 <- eval (isBitSet v_6636 7);
      v_6733 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6638 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 224 256) 24 8) (MInt2Float (extract v_6642 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6649 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 192 224) 24 8) (MInt2Float (extract v_6642 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6661 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 160 192) 24 8) (MInt2Float (extract v_6642 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6670 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6639 128 160) 24 8) (MInt2Float (extract v_6642 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3506) (concat (concat (concat (concat (mux v_6637 v_6683 (expression.bv_nat 32 0)) (mux v_6685 v_6683 (expression.bv_nat 32 0))) (mux v_6688 v_6683 (expression.bv_nat 32 0))) (mux v_6691 v_6683 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_6637 v_6733 (expression.bv_nat 32 0)) (mux v_6685 v_6733 (expression.bv_nat 32 0))) (mux v_6688 v_6733 (expression.bv_nat 32 0))) (mux v_6691 v_6733 (expression.bv_nat 32 0))));
      pure ()
    pat_end;
    pattern fun (v_3484 : imm int) (v_3485 : Mem) (v_3486 : reg (bv 128)) (v_3487 : reg (bv 128)) => do
      v_10551 <- eval (handleImmediateWithSignExtend v_3484 8 8);
      v_10554 <- getRegister v_3486;
      v_10557 <- evaluateAddress v_3485;
      v_10558 <- load v_10557 16;
      v_10599 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10551 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10554 96 128) 24 8) (MInt2Float (extract v_10558 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_10551 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10554 64 96) 24 8) (MInt2Float (extract v_10558 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10551 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10554 32 64) 24 8) (MInt2Float (extract v_10558 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_10551 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10554 0 32) 24 8) (MInt2Float (extract v_10558 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3487) (concat (concat (concat (mux (isBitSet v_10551 4) v_10599 (expression.bv_nat 32 0)) (mux (isBitSet v_10551 5) v_10599 (expression.bv_nat 32 0))) (mux (isBitSet v_10551 6) v_10599 (expression.bv_nat 32 0))) (mux (isBitSet v_10551 7) v_10599 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3497 : imm int) (v_3498 : Mem) (v_3499 : reg (bv 256)) (v_3500 : reg (bv 256)) => do
      v_10611 <- eval (handleImmediateWithSignExtend v_3497 8 8);
      v_10612 <- eval (isBitSet v_10611 4);
      v_10613 <- eval (isBitSet v_10611 3);
      v_10614 <- getRegister v_3499;
      v_10617 <- evaluateAddress v_3498;
      v_10618 <- load v_10617 32;
      v_10625 <- eval (isBitSet v_10611 2);
      v_10637 <- eval (isBitSet v_10611 1);
      v_10646 <- eval (isBitSet v_10611 0);
      v_10659 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10613 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 96 128) 24 8) (MInt2Float (extract v_10618 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10625 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 64 96) 24 8) (MInt2Float (extract v_10618 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10637 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 32 64) 24 8) (MInt2Float (extract v_10618 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10646 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 0 32) 24 8) (MInt2Float (extract v_10618 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_10661 <- eval (isBitSet v_10611 5);
      v_10664 <- eval (isBitSet v_10611 6);
      v_10667 <- eval (isBitSet v_10611 7);
      v_10709 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10613 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 224 256) 24 8) (MInt2Float (extract v_10618 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10625 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 192 224) 24 8) (MInt2Float (extract v_10618 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10637 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 160 192) 24 8) (MInt2Float (extract v_10618 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10646 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10614 128 160) 24 8) (MInt2Float (extract v_10618 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3500) (concat (concat (concat (concat (mux v_10612 v_10659 (expression.bv_nat 32 0)) (mux v_10661 v_10659 (expression.bv_nat 32 0))) (mux v_10664 v_10659 (expression.bv_nat 32 0))) (mux v_10667 v_10659 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_10612 v_10709 (expression.bv_nat 32 0)) (mux v_10661 v_10709 (expression.bv_nat 32 0))) (mux v_10664 v_10709 (expression.bv_nat 32 0))) (mux v_10667 v_10709 (expression.bv_nat 32 0))));
      pure ()
    pat_end
