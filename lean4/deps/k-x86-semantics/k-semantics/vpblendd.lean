def vpblendd1 : instruction :=
  definst "vpblendd" $ do
    pattern fun (v_2608 : imm int) (v_2612 : reg (bv 128)) (v_2613 : reg (bv 128)) (v_2614 : reg (bv 128)) => do
      v_6584 <- eval (handleImmediateWithSignExtend v_2608 8 8);
      v_6587 <- getRegister v_2613;
      v_6589 <- getRegister v_2612;
      setRegister (lhs.of_reg v_2614) (concat (mux (eq (extract v_6584 4 5) (expression.bv_nat 1 0)) (extract v_6587 0 32) (extract v_6589 0 32)) (concat (mux (eq (extract v_6584 5 6) (expression.bv_nat 1 0)) (extract v_6587 32 64) (extract v_6589 32 64)) (concat (mux (eq (extract v_6584 6 7) (expression.bv_nat 1 0)) (extract v_6587 64 96) (extract v_6589 64 96)) (mux (eq (extract v_6584 7 8) (expression.bv_nat 1 0)) (extract v_6587 96 128) (extract v_6589 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2621 : imm int) (v_2625 : reg (bv 256)) (v_2626 : reg (bv 256)) (v_2627 : reg (bv 256)) => do
      v_6617 <- eval (handleImmediateWithSignExtend v_2621 8 8);
      v_6620 <- getRegister v_2626;
      v_6622 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2627) (concat (mux (eq (extract v_6617 0 1) (expression.bv_nat 1 0)) (extract v_6620 0 32) (extract v_6622 0 32)) (concat (mux (eq (extract v_6617 1 2) (expression.bv_nat 1 0)) (extract v_6620 32 64) (extract v_6622 32 64)) (concat (mux (eq (extract v_6617 2 3) (expression.bv_nat 1 0)) (extract v_6620 64 96) (extract v_6622 64 96)) (concat (mux (eq (extract v_6617 3 4) (expression.bv_nat 1 0)) (extract v_6620 96 128) (extract v_6622 96 128)) (concat (mux (eq (extract v_6617 4 5) (expression.bv_nat 1 0)) (extract v_6620 128 160) (extract v_6622 128 160)) (concat (mux (eq (extract v_6617 5 6) (expression.bv_nat 1 0)) (extract v_6620 160 192) (extract v_6622 160 192)) (concat (mux (eq (extract v_6617 6 7) (expression.bv_nat 1 0)) (extract v_6620 192 224) (extract v_6622 192 224)) (mux (eq (extract v_6617 7 8) (expression.bv_nat 1 0)) (extract v_6620 224 256) (extract v_6622 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2602 : imm int) (v_2605 : Mem) (v_2606 : reg (bv 128)) (v_2607 : reg (bv 128)) => do
      v_15881 <- eval (handleImmediateWithSignExtend v_2602 8 8);
      v_15884 <- getRegister v_2606;
      v_15886 <- evaluateAddress v_2605;
      v_15887 <- load v_15886 16;
      setRegister (lhs.of_reg v_2607) (concat (mux (eq (extract v_15881 4 5) (expression.bv_nat 1 0)) (extract v_15884 0 32) (extract v_15887 0 32)) (concat (mux (eq (extract v_15881 5 6) (expression.bv_nat 1 0)) (extract v_15884 32 64) (extract v_15887 32 64)) (concat (mux (eq (extract v_15881 6 7) (expression.bv_nat 1 0)) (extract v_15884 64 96) (extract v_15887 64 96)) (mux (eq (extract v_15881 7 8) (expression.bv_nat 1 0)) (extract v_15884 96 128) (extract v_15887 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2615 : imm int) (v_2618 : Mem) (v_2619 : reg (bv 256)) (v_2620 : reg (bv 256)) => do
      v_15909 <- eval (handleImmediateWithSignExtend v_2615 8 8);
      v_15912 <- getRegister v_2619;
      v_15914 <- evaluateAddress v_2618;
      v_15915 <- load v_15914 32;
      setRegister (lhs.of_reg v_2620) (concat (mux (eq (extract v_15909 0 1) (expression.bv_nat 1 0)) (extract v_15912 0 32) (extract v_15915 0 32)) (concat (mux (eq (extract v_15909 1 2) (expression.bv_nat 1 0)) (extract v_15912 32 64) (extract v_15915 32 64)) (concat (mux (eq (extract v_15909 2 3) (expression.bv_nat 1 0)) (extract v_15912 64 96) (extract v_15915 64 96)) (concat (mux (eq (extract v_15909 3 4) (expression.bv_nat 1 0)) (extract v_15912 96 128) (extract v_15915 96 128)) (concat (mux (eq (extract v_15909 4 5) (expression.bv_nat 1 0)) (extract v_15912 128 160) (extract v_15915 128 160)) (concat (mux (eq (extract v_15909 5 6) (expression.bv_nat 1 0)) (extract v_15912 160 192) (extract v_15915 160 192)) (concat (mux (eq (extract v_15909 6 7) (expression.bv_nat 1 0)) (extract v_15912 192 224) (extract v_15915 192 224)) (mux (eq (extract v_15909 7 8) (expression.bv_nat 1 0)) (extract v_15912 224 256) (extract v_15915 224 256)))))))));
      pure ()
    pat_end
