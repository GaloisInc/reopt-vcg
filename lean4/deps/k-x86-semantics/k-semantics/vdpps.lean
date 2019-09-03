def vdpps1 : instruction :=
  definst "vdpps" $ do
    pattern fun (v_3424 : imm int) (v_3428 : reg (bv 128)) (v_3429 : reg (bv 128)) (v_3430 : reg (bv 128)) => do
      v_6653 <- eval (handleImmediateWithSignExtend v_3424 8 8);
      v_6658 <- getRegister v_3429;
      v_6661 <- getRegister v_3428;
      v_6705 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_6653 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6658 96 128) 24 8) (MInt2Float (extract v_6661 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_6653 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6658 64 96) 24 8) (MInt2Float (extract v_6661 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_6653 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6658 32 64) 24 8) (MInt2Float (extract v_6661 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_6653 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6658 0 32) 24 8) (MInt2Float (extract v_6661 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3430) (concat (concat (concat (mux (eq (extract v_6653 4 5) (expression.bv_nat 1 1)) v_6705 (expression.bv_nat 32 0)) (mux (eq (extract v_6653 5 6) (expression.bv_nat 1 1)) v_6705 (expression.bv_nat 32 0))) (mux (eq (extract v_6653 6 7) (expression.bv_nat 1 1)) v_6705 (expression.bv_nat 32 0))) (mux (eq (extract v_6653 7 8) (expression.bv_nat 1 1)) v_6705 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3437 : imm int) (v_3439 : reg (bv 256)) (v_3440 : reg (bv 256)) (v_3441 : reg (bv 256)) => do
      v_6726 <- eval (handleImmediateWithSignExtend v_3437 8 8);
      v_6728 <- eval (eq (extract v_6726 4 5) (expression.bv_nat 1 1));
      v_6730 <- eval (eq (extract v_6726 3 4) (expression.bv_nat 1 1));
      v_6731 <- getRegister v_3440;
      v_6734 <- getRegister v_3439;
      v_6742 <- eval (eq (extract v_6726 2 3) (expression.bv_nat 1 1));
      v_6755 <- eval (eq (extract v_6726 1 2) (expression.bv_nat 1 1));
      v_6765 <- eval (eq (extract v_6726 0 1) (expression.bv_nat 1 1));
      v_6778 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6730 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 96 128) 24 8) (MInt2Float (extract v_6734 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6742 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 64 96) 24 8) (MInt2Float (extract v_6734 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6755 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 32 64) 24 8) (MInt2Float (extract v_6734 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6765 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 0 32) 24 8) (MInt2Float (extract v_6734 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_6781 <- eval (eq (extract v_6726 5 6) (expression.bv_nat 1 1));
      v_6785 <- eval (eq (extract v_6726 6 7) (expression.bv_nat 1 1));
      v_6789 <- eval (eq (extract v_6726 7 8) (expression.bv_nat 1 1));
      v_6831 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6730 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 224 256) 24 8) (MInt2Float (extract v_6734 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6742 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 192 224) 24 8) (MInt2Float (extract v_6734 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_6755 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 160 192) 24 8) (MInt2Float (extract v_6734 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_6765 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_6731 128 160) 24 8) (MInt2Float (extract v_6734 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3441) (concat (concat (concat (concat (mux v_6728 v_6778 (expression.bv_nat 32 0)) (mux v_6781 v_6778 (expression.bv_nat 32 0))) (mux v_6785 v_6778 (expression.bv_nat 32 0))) (mux v_6789 v_6778 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_6728 v_6831 (expression.bv_nat 32 0)) (mux v_6781 v_6831 (expression.bv_nat 32 0))) (mux v_6785 v_6831 (expression.bv_nat 32 0))) (mux v_6789 v_6831 (expression.bv_nat 32 0))));
      pure ()
    pat_end;
    pattern fun (v_3419 : imm int) (v_3418 : Mem) (v_3422 : reg (bv 128)) (v_3423 : reg (bv 128)) => do
      v_10793 <- eval (handleImmediateWithSignExtend v_3419 8 8);
      v_10798 <- getRegister v_3422;
      v_10801 <- evaluateAddress v_3418;
      v_10802 <- load v_10801 16;
      v_10846 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_10793 3 4) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10798 96 128) 24 8) (MInt2Float (extract v_10802 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_10793 2 3) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10798 64 96) 24 8) (MInt2Float (extract v_10802 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux (eq (extract v_10793 1 2) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10798 32 64) 24 8) (MInt2Float (extract v_10802 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux (eq (extract v_10793 0 1) (expression.bv_nat 1 1)) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10798 0 32) 24 8) (MInt2Float (extract v_10802 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3423) (concat (concat (concat (mux (eq (extract v_10793 4 5) (expression.bv_nat 1 1)) v_10846 (expression.bv_nat 32 0)) (mux (eq (extract v_10793 5 6) (expression.bv_nat 1 1)) v_10846 (expression.bv_nat 32 0))) (mux (eq (extract v_10793 6 7) (expression.bv_nat 1 1)) v_10846 (expression.bv_nat 32 0))) (mux (eq (extract v_10793 7 8) (expression.bv_nat 1 1)) v_10846 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3432 : imm int) (v_3431 : Mem) (v_3433 : reg (bv 256)) (v_3434 : reg (bv 256)) => do
      v_10861 <- eval (handleImmediateWithSignExtend v_3432 8 8);
      v_10863 <- eval (eq (extract v_10861 4 5) (expression.bv_nat 1 1));
      v_10865 <- eval (eq (extract v_10861 3 4) (expression.bv_nat 1 1));
      v_10866 <- getRegister v_3433;
      v_10869 <- evaluateAddress v_3431;
      v_10870 <- load v_10869 32;
      v_10878 <- eval (eq (extract v_10861 2 3) (expression.bv_nat 1 1));
      v_10891 <- eval (eq (extract v_10861 1 2) (expression.bv_nat 1 1));
      v_10901 <- eval (eq (extract v_10861 0 1) (expression.bv_nat 1 1));
      v_10914 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10865 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 96 128) 24 8) (MInt2Float (extract v_10870 96 128) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10878 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 64 96) 24 8) (MInt2Float (extract v_10870 64 96) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10891 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 32 64) 24 8) (MInt2Float (extract v_10870 32 64) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10901 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 0 32) 24 8) (MInt2Float (extract v_10870 0 32) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      v_10917 <- eval (eq (extract v_10861 5 6) (expression.bv_nat 1 1));
      v_10921 <- eval (eq (extract v_10861 6 7) (expression.bv_nat 1 1));
      v_10925 <- eval (eq (extract v_10861 7 8) (expression.bv_nat 1 1));
      v_10967 <- eval (Float2MInt (_+Float__FLOAT (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10865 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 224 256) 24 8) (MInt2Float (extract v_10870 224 256) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10878 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 192 224) 24 8) (MInt2Float (extract v_10870 192 224) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8) (MInt2Float (Float2MInt (_+Float__FLOAT (MInt2Float (mux v_10891 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 160 192) 24 8) (MInt2Float (extract v_10870 160 192) 24 8)) 32) (expression.bv_nat 32 0)) 24 8) (MInt2Float (mux v_10901 (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10866 128 160) 24 8) (MInt2Float (extract v_10870 128 160) 24 8)) 32) (expression.bv_nat 32 0)) 24 8)) 32) 24 8)) 32);
      setRegister (lhs.of_reg v_3434) (concat (concat (concat (concat (mux v_10863 v_10914 (expression.bv_nat 32 0)) (mux v_10917 v_10914 (expression.bv_nat 32 0))) (mux v_10921 v_10914 (expression.bv_nat 32 0))) (mux v_10925 v_10914 (expression.bv_nat 32 0))) (concat (concat (concat (mux v_10863 v_10967 (expression.bv_nat 32 0)) (mux v_10917 v_10967 (expression.bv_nat 32 0))) (mux v_10921 v_10967 (expression.bv_nat 32 0))) (mux v_10925 v_10967 (expression.bv_nat 32 0))));
      pure ()
    pat_end
