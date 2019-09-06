def vdpps1 : instruction :=
  definst "vdpps" $ do
    pattern fun (v_3515 : imm int) (v_3519 : reg (bv 128)) (v_3520 : reg (bv 128)) (v_3521 : reg (bv 128)) => do
      v_6598 <- eval (handleImmediateWithSignExtend v_3515 8 8);
      v_6601 <- getRegister v_3520;
      v_6604 <- getRegister v_3519;
      v_6645 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6598 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6601 96 128) 24 8) (MInt2Float (extract v_6604 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_6598 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6601 64 96) 24 8) (MInt2Float (extract v_6604 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_6598 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6601 32 64) 24 8) (MInt2Float (extract v_6604 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_6598 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6601 0 32) 24 8) (MInt2Float (extract v_6604 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3521) (concat (concat (concat (mux (isBitSet v_6598 4) v_6645 (expression.bv_nat 32 0)) (mux (isBitSet v_6598 5) v_6645 (expression.bv_nat 32 0))) (mux (isBitSet v_6598 6) v_6645 (expression.bv_nat 32 0))) (mux (isBitSet v_6598 7) v_6645 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3528 : imm int) (v_3529 : reg (bv 256)) (v_3530 : reg (bv 256)) (v_3531 : reg (bv 256)) => do
      v_6663 <- eval (handleImmediateWithSignExtend v_3528 8 8);
      v_6664 <- eval (isBitSet v_6663 4);
      v_6665 <- eval (isBitSet v_6663 3);
      v_6666 <- getRegister v_3530;
      v_6669 <- getRegister v_3529;
      v_6676 <- eval (isBitSet v_6663 2);
      v_6688 <- eval (isBitSet v_6663 1);
      v_6697 <- eval (isBitSet v_6663 0);
      v_6710 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6665 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 96 128) 24 8) (MInt2Float (extract v_6669 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6676 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 64 96) 24 8) (MInt2Float (extract v_6669 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6688 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 32 64) 24 8) (MInt2Float (extract v_6669 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6697 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 0 32) 24 8) (MInt2Float (extract v_6669 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_6712 <- eval (isBitSet v_6663 5);
      v_6715 <- eval (isBitSet v_6663 6);
      v_6718 <- eval (isBitSet v_6663 7);
      v_6760 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6665 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 224 256) 24 8) (MInt2Float (extract v_6669 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6676 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 192 224) 24 8) (MInt2Float (extract v_6669 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6688 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 160 192) 24 8) (MInt2Float (extract v_6669 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6697 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6666 128 160) 24 8) (MInt2Float (extract v_6669 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3531) (concat (concat (concat (concat (mux v_6664 v_6710 (expression.bv_nat 32 0)) (mux v_6712 v_6710 (expression.bv_nat 32 0))) (mux v_6715 v_6710 (expression.bv_nat 32 0))) (mux v_6718 v_6710 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_6664 v_6760 (expression.bv_nat 32 0)) (mux v_6712 v_6760 (expression.bv_nat 32 0))) (mux v_6715 v_6760 (expression.bv_nat 32 0))) (mux v_6718 v_6760 (expression.bv_nat 32 0))));
      pure ()
    pat_end;
    pattern fun (v_3509 : imm int) (v_3510 : Mem) (v_3513 : reg (bv 128)) (v_3514 : reg (bv 128)) => do
      v_10578 <- eval (handleImmediateWithSignExtend v_3509 8 8);
      v_10581 <- getRegister v_3513;
      v_10584 <- evaluateAddress v_3510;
      v_10585 <- load v_10584 16;
      v_10626 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10578 3) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10581 96 128) 24 8) (MInt2Float (extract v_10585 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_10578 2) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10581 64 96) 24 8) (MInt2Float (extract v_10585 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (isBitSet v_10578 1) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10581 32 64) 24 8) (MInt2Float (extract v_10585 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (isBitSet v_10578 0) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10581 0 32) 24 8) (MInt2Float (extract v_10585 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3514) (concat (concat (concat (mux (isBitSet v_10578 4) v_10626 (expression.bv_nat 32 0)) (mux (isBitSet v_10578 5) v_10626 (expression.bv_nat 32 0))) (mux (isBitSet v_10578 6) v_10626 (expression.bv_nat 32 0))) (mux (isBitSet v_10578 7) v_10626 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3522 : imm int) (v_3523 : Mem) (v_3524 : reg (bv 256)) (v_3525 : reg (bv 256)) => do
      v_10638 <- eval (handleImmediateWithSignExtend v_3522 8 8);
      v_10639 <- eval (isBitSet v_10638 4);
      v_10640 <- eval (isBitSet v_10638 3);
      v_10641 <- getRegister v_3524;
      v_10644 <- evaluateAddress v_3523;
      v_10645 <- load v_10644 32;
      v_10652 <- eval (isBitSet v_10638 2);
      v_10664 <- eval (isBitSet v_10638 1);
      v_10673 <- eval (isBitSet v_10638 0);
      v_10686 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10640 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 96 128) 24 8) (MInt2Float (extract v_10645 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10652 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 64 96) 24 8) (MInt2Float (extract v_10645 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10664 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 32 64) 24 8) (MInt2Float (extract v_10645 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10673 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 0 32) 24 8) (MInt2Float (extract v_10645 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_10688 <- eval (isBitSet v_10638 5);
      v_10691 <- eval (isBitSet v_10638 6);
      v_10694 <- eval (isBitSet v_10638 7);
      v_10736 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10640 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 224 256) 24 8) (MInt2Float (extract v_10645 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10652 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 192 224) 24 8) (MInt2Float (extract v_10645 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10664 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 160 192) 24 8) (MInt2Float (extract v_10645 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10673 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10641 128 160) 24 8) (MInt2Float (extract v_10645 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3525) (concat (concat (concat (concat (mux v_10639 v_10686 (expression.bv_nat 32 0)) (mux v_10688 v_10686 (expression.bv_nat 32 0))) (mux v_10691 v_10686 (expression.bv_nat 32 0))) (mux v_10694 v_10686 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_10639 v_10736 (expression.bv_nat 32 0)) (mux v_10688 v_10736 (expression.bv_nat 32 0))) (mux v_10691 v_10736 (expression.bv_nat 32 0))) (mux v_10694 v_10736 (expression.bv_nat 32 0))));
      pure ()
    pat_end
