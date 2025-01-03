use crate::en::{EntriesEncoder, MapEncoder};
use crate::{Context, Writer};

use super::{JsonEncoder, JsonObjectKeyEncoder, JsonObjectPairEncoder};

/// An object encoder for JSON.
pub(crate) struct JsonObjectEncoder<W, C> {
    cx: C,
    len: usize,
    end: &'static [u8],
    writer: W,
}

impl<W, C> JsonObjectEncoder<W, C>
where
    W: Writer,
    C: Context,
{
    #[inline]
    pub(super) fn new(cx: C, writer: W) -> Result<Self, C::Error> {
        Self::with_end(cx, writer, b"}")
    }

    #[inline]
    pub(super) fn with_end(cx: C, mut writer: W, end: &'static [u8]) -> Result<Self, C::Error> {
        writer.write_byte(cx, b'{')?;

        Ok(Self {
            cx,
            len: 0,
            end,
            writer,
        })
    }
}

impl<W, C> MapEncoder for JsonObjectEncoder<W, C>
where
    W: Writer,
    C: Context,
{
    type Cx = C;
    type Ok = ();
    type EncodeEntry<'this>
        = JsonObjectPairEncoder<W::Mut<'this>, C>
    where
        Self: 'this;

    #[inline]
    fn cx(&self) -> Self::Cx {
        self.cx
    }

    #[inline]
    fn encode_entry(&mut self) -> Result<Self::EncodeEntry<'_>, C::Error> {
        self.len += 1;

        Ok(JsonObjectPairEncoder::new(
            self.cx,
            self.len == 1,
            self.writer.borrow_mut(),
        ))
    }

    #[inline]
    fn finish_map(mut self) -> Result<Self::Ok, C::Error> {
        self.writer.write_bytes(self.cx, self.end)
    }
}

impl<W, C> EntriesEncoder for JsonObjectEncoder<W, C>
where
    W: Writer,
    C: Context,
{
    type Cx = C;
    type Ok = ();
    type EncodeEntryKey<'this>
        = JsonObjectKeyEncoder<W::Mut<'this>, C>
    where
        Self: 'this;
    type EncodeEntryValue<'this>
        = JsonEncoder<W::Mut<'this>, C>
    where
        Self: 'this;

    #[inline]
    fn cx(&self) -> Self::Cx {
        self.cx
    }

    #[inline]
    fn encode_entry_key(&mut self) -> Result<Self::EncodeEntryKey<'_>, C::Error> {
        if self.len > 0 {
            self.writer.write_byte(self.cx, b',')?;
        }

        self.len += 1;
        Ok(JsonObjectKeyEncoder::new(self.cx, self.writer.borrow_mut()))
    }

    #[inline]
    fn encode_entry_value(&mut self) -> Result<Self::EncodeEntryValue<'_>, C::Error> {
        self.writer.write_byte(self.cx, b':')?;
        Ok(JsonEncoder::new(self.cx, self.writer.borrow_mut()))
    }

    #[inline]
    fn finish_entries(mut self) -> Result<Self::Ok, C::Error> {
        self.writer.write_byte(self.cx, b'}')
    }
}
