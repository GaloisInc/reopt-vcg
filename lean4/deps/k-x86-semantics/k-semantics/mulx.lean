def mulx1 : instruction :=
  definst "mulx" $ do
    pattern fun (v_2796 : reg (bv 32)) (v_2797 : reg (bv 32)) (v_2798 : reg (bv 32)) => do
      v_7191 <- getRegister rdx;
      v_7194 <- getRegister v_2796;
      v_7196 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_7191 32 64)) (concat (expression.bv_nat 32 0) v_7194));
      setRegister (lhs.of_reg v_2797) (extract v_7196 32 64);
      setRegister (lhs.of_reg v_2798) (extract v_7196 0 32);
      pure ()
    pat_end;
    pattern fun (v_2817 : reg (bv 64)) (v_2818 : reg (bv 64)) (v_2819 : reg (bv 64)) => do
      v_7212 <- getRegister rdx;
      v_7214 <- getRegister v_2817;
      v_7216 <- eval (mul (concat (expression.bv_nat 64 0) v_7212) (concat (expression.bv_nat 64 0) v_7214));
      setRegister (lhs.of_reg v_2818) (extract v_7216 64 128);
      setRegister (lhs.of_reg v_2819) (extract v_7216 0 64);
      pure ()
    pat_end;
    pattern fun (v_2786 : Mem) (v_2787 : reg (bv 32)) (v_2788 : reg (bv 32)) => do
      v_10959 <- evaluateAddress v_2786;
      v_10962 <- load v_10959 4;
      v_10964 <- eval (mul (concat (expression.bv_nat 32 0) (extract v_10959 32 64)) (concat (expression.bv_nat 32 0) v_10962));
      setRegister (lhs.of_reg v_2787) (extract v_10964 32 64);
      setRegister (lhs.of_reg v_2788) (extract v_10964 0 32);
      pure ()
    pat_end;
    pattern fun (v_2807 : Mem) (v_2808 : reg (bv 64)) (v_2809 : reg (bv 64)) => do
      v_10969 <- evaluateAddress v_2807;
      v_10971 <- load v_10969 8;
      v_10973 <- eval (mul (concat (expression.bv_nat 64 0) v_10969) (concat (expression.bv_nat 64 0) v_10971));
      setRegister (lhs.of_reg v_2808) (extract v_10973 64 128);
      setRegister (lhs.of_reg v_2809) (extract v_10973 0 64);
      pure ()
    pat_end
