def mulx1 : instruction :=
  definst "mulx" $ do
    pattern fun (v_2846 : reg (bv 32)) (v_2847 : reg (bv 32)) (v_2848 : reg (bv 32)) => do
      v_7055 <- getRegister rdx;
      v_7058 <- getRegister v_2846;
      v_7060 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_7055 32 64)) (concat (expression.bv_nat 32 0) v_7058));
      setRegister (lhs.of_reg v_2848) (extract v_7060 0 32);
      setRegister (lhs.of_reg v_2847) (extract v_7060 32 64);
      pure ()
    pat_end;
    pattern fun (v_2867 : reg (bv 64)) (v_2868 : reg (bv 64)) (v_2869 : reg (bv 64)) => do
      v_7076 <- getRegister rdx;
      v_7078 <- getRegister v_2867;
      v_7080 <- eval (mul (concat (expression.bv_nat 64 0) v_7076) (concat (expression.bv_nat 64 0) v_7078));
      setRegister (lhs.of_reg v_2869) (extract v_7080 0 64);
      setRegister (lhs.of_reg v_2868) (extract v_7080 64 128);
      pure ()
    pat_end;
    pattern fun (v_2836 : Mem) (v_2837 : reg (bv 32)) (v_2838 : reg (bv 32)) => do
      v_10674 <- evaluateAddress v_2836;
      v_10677 <- load v_10674 4;
      v_10679 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_10674 32 64)) (concat (expression.bv_nat 32 0) v_10677));
      setRegister (lhs.of_reg v_2837) (extract v_10679 32 64);
      setRegister (lhs.of_reg v_2838) (extract v_10679 0 32);
      pure ()
    pat_end;
    pattern fun (v_2859 : Mem) (v_2857 : reg (bv 64)) (v_2858 : reg (bv 64)) => do
      v_10684 <- evaluateAddress v_2859;
      v_10686 <- load v_10684 8;
      v_10688 <- eval (mul (concat (expression.bv_nat 64 0) v_10684) (concat (expression.bv_nat 64 0) v_10686));
      setRegister (lhs.of_reg v_2858) (extract v_10688 0 64);
      setRegister (lhs.of_reg v_2857) (extract v_10688 64 128);
      pure ()
    pat_end
