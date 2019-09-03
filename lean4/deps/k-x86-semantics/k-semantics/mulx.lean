def mulx1 : instruction :=
  definst "mulx" $ do
    pattern fun (v_2783 : reg (bv 32)) (v_2784 : reg (bv 32)) (v_2785 : reg (bv 32)) => do
      v_7211 <- getRegister rdx;
      v_7214 <- getRegister v_2783;
      v_7216 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_7211 32 64)) (concat (expression.bv_nat 32 0) v_7214));
      setRegister (lhs.of_reg v_2785) (extract v_7216 0 32);
      setRegister (lhs.of_reg v_2784) (extract v_7216 32 64);
      pure ()
    pat_end;
    pattern fun (v_2804 : reg (bv 64)) (v_2805 : reg (bv 64)) (v_2806 : reg (bv 64)) => do
      v_7232 <- getRegister rdx;
      v_7234 <- getRegister v_2804;
      v_7236 <- eval (mul (concat (expression.bv_nat 64 0) v_7232) (concat (expression.bv_nat 64 0) v_7234));
      setRegister (lhs.of_reg v_2805) (extract v_7236 64 128);
      setRegister (lhs.of_reg v_2806) (extract v_7236 0 64);
      pure ()
    pat_end;
    pattern fun (v_2773 : Mem) (v_2774 : reg (bv 32)) (v_2775 : reg (bv 32)) => do
      v_10991 <- evaluateAddress v_2773;
      v_10994 <- load v_10991 4;
      v_10996 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_10991 32 64)) (concat (expression.bv_nat 32 0) v_10994));
      setRegister (lhs.of_reg v_2774) (extract v_10996 32 64);
      setRegister (lhs.of_reg v_2775) (extract v_10996 0 32);
      pure ()
    pat_end;
    pattern fun (v_2794 : Mem) (v_2795 : reg (bv 64)) (v_2796 : reg (bv 64)) => do
      v_11001 <- evaluateAddress v_2794;
      v_11003 <- load v_11001 8;
      v_11005 <- eval (mul (concat (expression.bv_nat 64 0) v_11001) (concat (expression.bv_nat 64 0) v_11003));
      setRegister (lhs.of_reg v_2795) (extract v_11005 64 128);
      setRegister (lhs.of_reg v_2796) (extract v_11005 0 64);
      pure ()
    pat_end
