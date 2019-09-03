def vmovmskps1 : instruction :=
  definst "vmovmskps" $ do
    pattern fun (v_2875 : reg (bv 128)) (v_2874 : reg (bv 32)) => do
      v_4861 <- getRegister v_2875;
      setRegister (lhs.of_reg v_2874) (concat (expression.bv_nat 28 0) (concat (extract v_4861 0 1) (concat (extract v_4861 32 33) (concat (extract v_4861 64 65) (extract v_4861 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2880 : reg (bv 256)) (v_2879 : reg (bv 32)) => do
      v_4871 <- getRegister v_2880;
      setRegister (lhs.of_reg v_2879) (concat (expression.bv_nat 24 0) (concat (extract v_4871 0 1) (concat (extract v_4871 32 33) (concat (extract v_4871 64 65) (concat (extract v_4871 96 97) (concat (extract v_4871 128 129) (concat (extract v_4871 160 161) (concat (extract v_4871 192 193) (extract v_4871 224 225)))))))));
      pure ()
    pat_end;
    pattern fun (v_2885 : reg (bv 128)) (v_2883 : reg (bv 64)) => do
      v_4889 <- getRegister v_2885;
      setRegister (lhs.of_reg v_2883) (concat (expression.bv_nat 60 0) (concat (extract v_4889 0 1) (concat (extract v_4889 32 33) (concat (extract v_4889 64 65) (extract v_4889 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2890 : reg (bv 256)) (v_2888 : reg (bv 64)) => do
      v_4899 <- getRegister v_2890;
      setRegister (lhs.of_reg v_2888) (concat (expression.bv_nat 56 0) (concat (extract v_4899 0 1) (concat (extract v_4899 32 33) (concat (extract v_4899 64 65) (concat (extract v_4899 96 97) (concat (extract v_4899 128 129) (concat (extract v_4899 160 161) (concat (extract v_4899 192 193) (extract v_4899 224 225)))))))));
      pure ()
    pat_end
