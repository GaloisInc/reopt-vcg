def vmovmskps1 : instruction :=
  definst "vmovmskps" $ do
    pattern fun (v_2938 : reg (bv 128)) (v_2937 : reg (bv 32)) => do
      v_4919 <- getRegister v_2938;
      setRegister (lhs.of_reg v_2937) (concat (expression.bv_nat 28 0) (concat (extract v_4919 0 1) (concat (extract v_4919 32 33) (concat (extract v_4919 64 65) (extract v_4919 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2944 : reg (bv 256)) (v_2942 : reg (bv 32)) => do
      v_4929 <- getRegister v_2944;
      setRegister (lhs.of_reg v_2942) (concat (expression.bv_nat 24 0) (concat (extract v_4929 0 1) (concat (extract v_4929 32 33) (concat (extract v_4929 64 65) (concat (extract v_4929 96 97) (concat (extract v_4929 128 129) (concat (extract v_4929 160 161) (concat (extract v_4929 192 193) (extract v_4929 224 225)))))))));
      pure ()
    pat_end;
    pattern fun (v_2947 : reg (bv 128)) (v_2948 : reg (bv 64)) => do
      v_4947 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2948) (concat (expression.bv_nat 60 0) (concat (extract v_4947 0 1) (concat (extract v_4947 32 33) (concat (extract v_4947 64 65) (extract v_4947 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2954 : reg (bv 256)) (v_2952 : reg (bv 64)) => do
      v_4957 <- getRegister v_2954;
      setRegister (lhs.of_reg v_2952) (concat (expression.bv_nat 56 0) (concat (extract v_4957 0 1) (concat (extract v_4957 32 33) (concat (extract v_4957 64 65) (concat (extract v_4957 96 97) (concat (extract v_4957 128 129) (concat (extract v_4957 160 161) (concat (extract v_4957 192 193) (extract v_4957 224 225)))))))));
      pure ()
    pat_end
