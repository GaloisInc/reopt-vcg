def vmovmskps1 : instruction :=
  definst "vmovmskps" $ do
    pattern fun (v_2963 : reg (bv 128)) (v_2962 : reg (bv 32)) => do
      v_4946 <- getRegister v_2963;
      setRegister (lhs.of_reg v_2962) (concat (expression.bv_nat 28 0) (concat (extract v_4946 0 1) (concat (extract v_4946 32 33) (concat (extract v_4946 64 65) (extract v_4946 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2968 : reg (bv 256)) (v_2967 : reg (bv 32)) => do
      v_4956 <- getRegister v_2968;
      setRegister (lhs.of_reg v_2967) (concat (expression.bv_nat 24 0) (concat (extract v_4956 0 1) (concat (extract v_4956 32 33) (concat (extract v_4956 64 65) (concat (extract v_4956 96 97) (concat (extract v_4956 128 129) (concat (extract v_4956 160 161) (concat (extract v_4956 192 193) (extract v_4956 224 225)))))))));
      pure ()
    pat_end;
    pattern fun (v_2973 : reg (bv 128)) (v_2972 : reg (bv 64)) => do
      v_4974 <- getRegister v_2973;
      setRegister (lhs.of_reg v_2972) (concat (expression.bv_nat 60 0) (concat (extract v_4974 0 1) (concat (extract v_4974 32 33) (concat (extract v_4974 64 65) (extract v_4974 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2978 : reg (bv 256)) (v_2977 : reg (bv 64)) => do
      v_4984 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2977) (concat (expression.bv_nat 56 0) (concat (extract v_4984 0 1) (concat (extract v_4984 32 33) (concat (extract v_4984 64 65) (concat (extract v_4984 96 97) (concat (extract v_4984 128 129) (concat (extract v_4984 160 161) (concat (extract v_4984 192 193) (extract v_4984 224 225)))))))));
      pure ()
    pat_end
