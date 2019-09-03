def vmovmskps1 : instruction :=
  definst "vmovmskps" $ do
    pattern fun (v_2886 : reg (bv 128)) (v_2888 : reg (bv 32)) => do
      v_5234 <- getRegister v_2886;
      setRegister (lhs.of_reg v_2888) (concat (expression.bv_nat 28 0) (concat (extract v_5234 0 1) (concat (extract v_5234 32 33) (concat (extract v_5234 64 65) (extract v_5234 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2891 : reg (bv 256)) (v_2893 : reg (bv 32)) => do
      v_5244 <- getRegister v_2891;
      setRegister (lhs.of_reg v_2893) (concat (expression.bv_nat 24 0) (concat (extract v_5244 0 1) (concat (extract v_5244 32 33) (concat (extract v_5244 64 65) (concat (extract v_5244 96 97) (concat (extract v_5244 128 129) (concat (extract v_5244 160 161) (concat (extract v_5244 192 193) (extract v_5244 224 225)))))))));
      pure ()
    pat_end;
    pattern fun (v_2896 : reg (bv 128)) (v_2898 : reg (bv 64)) => do
      v_5262 <- getRegister v_2896;
      setRegister (lhs.of_reg v_2898) (concat (expression.bv_nat 60 0) (concat (extract v_5262 0 1) (concat (extract v_5262 32 33) (concat (extract v_5262 64 65) (extract v_5262 96 97)))));
      pure ()
    pat_end;
    pattern fun (v_2901 : reg (bv 256)) (v_2903 : reg (bv 64)) => do
      v_5272 <- getRegister v_2901;
      setRegister (lhs.of_reg v_2903) (concat (expression.bv_nat 56 0) (concat (extract v_5272 0 1) (concat (extract v_5272 32 33) (concat (extract v_5272 64 65) (concat (extract v_5272 96 97) (concat (extract v_5272 128 129) (concat (extract v_5272 160 161) (concat (extract v_5272 192 193) (extract v_5272 224 225)))))))));
      pure ()
    pat_end
