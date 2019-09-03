def paddd1 : instruction :=
  definst "paddd" $ do
    pattern fun (v_3132 : reg (bv 128)) (v_3133 : reg (bv 128)) => do
      v_5775 <- getRegister v_3133;
      v_5777 <- getRegister v_3132;
      setRegister (lhs.of_reg v_3133) (concat (add (extract v_5775 0 32) (extract v_5777 0 32)) (concat (add (extract v_5775 32 64) (extract v_5777 32 64)) (concat (add (extract v_5775 64 96) (extract v_5777 64 96)) (add (extract v_5775 96 128) (extract v_5777 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3128 : Mem) (v_3129 : reg (bv 128)) => do
      v_9856 <- getRegister v_3129;
      v_9858 <- evaluateAddress v_3128;
      v_9859 <- load v_9858 16;
      setRegister (lhs.of_reg v_3129) (concat (add (extract v_9856 0 32) (extract v_9859 0 32)) (concat (add (extract v_9856 32 64) (extract v_9859 32 64)) (concat (add (extract v_9856 64 96) (extract v_9859 64 96)) (add (extract v_9856 96 128) (extract v_9859 96 128)))));
      pure ()
    pat_end
