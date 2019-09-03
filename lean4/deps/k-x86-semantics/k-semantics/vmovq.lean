def vmovq1 : instruction :=
  definst "vmovq" $ do
    pattern fun (v_2942 : reg (bv 128)) (v_2944 : reg (bv 64)) => do
      v_5326 <- getRegister v_2942;
      setRegister (lhs.of_reg v_2944) (extract v_5326 64 128);
      pure ()
    pat_end;
    pattern fun (v_2953 : reg (bv 64)) (v_2951 : reg (bv 128)) => do
      v_5333 <- getRegister v_2953;
      setRegister (lhs.of_reg v_2951) (concat (expression.bv_nat 64 0) v_5333);
      pure ()
    pat_end;
    pattern fun (v_2956 : reg (bv 128)) (v_2957 : reg (bv 128)) => do
      v_5336 <- getRegister v_2956;
      setRegister (lhs.of_reg v_2957) (concat (expression.bv_nat 64 0) (extract v_5336 64 128));
      pure ()
    pat_end;
    pattern fun (v_2939 : reg (bv 128)) (v_2938 : Mem) => do
      v_9941 <- evaluateAddress v_2938;
      v_9942 <- getRegister v_2939;
      store v_9941 (extract v_9942 64 128) 8;
      pure ()
    pat_end;
    pattern fun (v_2947 : Mem) (v_2948 : reg (bv 128)) => do
      v_11151 <- evaluateAddress v_2947;
      v_11152 <- load v_11151 8;
      setRegister (lhs.of_reg v_2948) (concat (expression.bv_nat 64 0) v_11152);
      pure ()
    pat_end
