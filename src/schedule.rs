use nom::*;
use std::str::{self, FromStr};
use std::collections::BTreeSet;
use chrono::{Utc, DateTime, Duration, Datelike, Timelike};
use chrono::offset::TimeZone;
use std::iter::{self, Iterator};
use error::{Error, ErrorKind};

use time_unit::*;

pub struct Schedule {
    years: Years,
    days_of_week: DaysOfWeek,
    months: Months,
    days_of_month: DaysOfMonth,
    hours: Hours,
    minutes: Minutes,
    seconds: Seconds,
}

impl Schedule {
    fn from_field_list(fields: Vec<Field>) -> Result<Schedule, Error> {
        let number_of_fields = fields.len();
        if number_of_fields != 6 && number_of_fields != 7 {
            bail!(ErrorKind::Expression(format!("Expression has {} fields. Valid cron \
                                                expressions have 6 or 7.",
                                                number_of_fields)));
        }

        let mut iter = fields.into_iter();

        let seconds = Seconds::from_field(iter.next().unwrap())?;
        let minutes = Minutes::from_field(iter.next().unwrap())?;
        let hours = Hours::from_field(iter.next().unwrap())?;
        let days_of_month = DaysOfMonth::from_field(iter.next().unwrap())?;
        let months = Months::from_field(iter.next().unwrap())?;
        let days_of_week = DaysOfWeek::from_field(iter.next().unwrap())?;
        let years: Years = iter.next()
            .map(Years::from_field)
            .unwrap_or_else(|| Ok(Years::all()))?;

        Ok(Schedule::from(seconds,
                          minutes,
                          hours,
                          days_of_month,
                          months,
                          days_of_week,
                          years))
    }

    fn from(seconds: Seconds,
            minutes: Minutes,
            hours: Hours,
            days_of_month: DaysOfMonth,
            months: Months,
            days_of_week: DaysOfWeek,
            years: Years)
            -> Schedule {
        Schedule {
            years: years,
            days_of_week: days_of_week,
            months: months,
            days_of_month: days_of_month,
            hours: hours,
            minutes: minutes,
            seconds: seconds,
        }
    }

    fn next_after<Z>(&self, after: &DateTime<Z>) -> Option<DateTime<Z>>
        where Z: TimeZone
    {
        use chrono::Duration;
        let mut datetime = after.clone() + Duration::seconds(1);

        loop {
            let year = datetime.year();
            if self.years.ordinals().range((year as u32)..).next().is_none() {
                return None;
            }
            if !self.years.ordinals().contains(&(year as u32)) {
                datetime = after.timezone().ymd(year+1, 1, 1).and_hms(0, 0, 0);
                continue;
            }
            let month = datetime.month();
            if !self.months.ordinals().contains(&month) {
                datetime = if month == 12 {
                    after.timezone().ymd(year+1, 1, 1).and_hms(0, 0, 0)
                } else {
                    after.timezone().ymd(year, month+1, 1).and_hms(0, 0, 0)
                };
                continue;
            }
            if !self.days_of_month.ordinals().contains(&datetime.day()) {
                datetime = datetime + Duration::days(1);
                datetime = datetime
                    .with_second(0)
                    .and_then(|datetime| datetime.with_minute(0))
                    .and_then(|datetime| datetime.with_hour(0))
                    .unwrap();
                continue;
            }
            if !self.days_of_week.ordinals().contains(&datetime.weekday().number_from_sunday()) {
                datetime = datetime + Duration::days(1);
                datetime = datetime
                    .with_second(0)
                    .and_then(|datetime| datetime.with_minute(0))
                    .and_then(|datetime| datetime.with_hour(0))
                    .unwrap();
                continue;
            }
            if !self.hours.ordinals().contains(&datetime.hour()) {
                datetime = datetime + Duration::hours(1);
                datetime = datetime.with_second(0).and_then(|datetime| datetime.with_minute(0)).unwrap();
                continue;
            }
            if !self.minutes.ordinals().contains(&datetime.minute()) {
                datetime = datetime + Duration::minutes(1);
                datetime = datetime.with_second(0).unwrap();
                continue;
            }
            if !self.seconds.ordinals().contains(&datetime.second()) {
                datetime = datetime + Duration::seconds(1);
                continue;
            }
            break;
        }
        datetime.with_nanosecond(0)
    }

  /// Provides an iterator which will return each DateTime that matches the schedule starting with
  /// the current time if applicable.
    pub fn upcoming<Z>(&self, timezone: Z) -> ScheduleIterator<Z>
        where Z: TimeZone
    {
        self.after(&timezone.from_utc_datetime(&Utc::now().naive_utc()))
    }

  /// Like the `upcoming` method, but allows you to specify a start time other than the present.
    pub fn after<'a, Z>(&'a self, after: &DateTime<Z>) -> ScheduleIterator<'a, Z>
        where Z: TimeZone
    {
        ScheduleIterator::new(self, after)
    }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the years included
  /// in this [Schedule](struct.Schedule.html).
  pub fn years(&self) -> &impl TimeUnitSpec {
    &self.years
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the months of the year included
  /// in this [Schedule](struct.Schedule.html).
  pub fn months(&self) -> &impl TimeUnitSpec {
    &self.months
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the days of the month included
  /// in this [Schedule](struct.Schedule.html).
  pub fn days_of_month(&self) -> &impl TimeUnitSpec {
    &self.days_of_month
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the days of the week included
  /// in this [Schedule](struct.Schedule.html).
  pub fn days_of_week(&self) -> &impl TimeUnitSpec {
    &self.days_of_week
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the hours of the day included
  /// in this [Schedule](struct.Schedule.html).
  pub fn hours(&self) -> &impl TimeUnitSpec {
    &self.hours
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the minutes of the hour included
  /// in this [Schedule](struct.Schedule.html).
  pub fn minutes(&self) -> &impl TimeUnitSpec {
    &self.minutes
  }

  /// Returns a [TimeUnitSpec](trait.TimeUnitSpec.html) describing the seconds of the minute included
  /// in this [Schedule](struct.Schedule.html).
  pub fn seconds(&self) -> &impl TimeUnitSpec {
    &self.seconds
  }
}

impl FromStr for Schedule {
    type Err = Error;
    fn from_str(expression: &str) -> Result<Self, Self::Err> {
        use nom::IResult::*;
        match schedule(expression.as_bytes()) {
            Done(_, schedule) => Ok(schedule), // Extract from nom tuple
            Error(_) => bail!(ErrorKind::Expression("Invalid cron expression.".to_owned())), //TODO: Details
            Incomplete(_) => bail!(ErrorKind::Expression("Incomplete cron expression.".to_owned())),
        }
    }
}

pub struct ScheduleIterator<'a, Z>
    where Z: TimeZone
{
    is_done: bool,
    schedule: &'a Schedule,
    previous_datetime: DateTime<Z>,
}
//TODO: Cutoff datetime?

impl<'a, Z> ScheduleIterator<'a, Z>
    where Z: TimeZone
{
    fn new(schedule: &'a Schedule, starting_datetime: &DateTime<Z>) -> ScheduleIterator<'a, Z> {
        ScheduleIterator {
            is_done: false,
            schedule: schedule,
            previous_datetime: starting_datetime.clone(),
        }
    }
}

impl<'a, Z> Iterator for ScheduleIterator<'a, Z>
    where Z: TimeZone
{
    type Item = DateTime<Z>;

    fn next(&mut self) -> Option<DateTime<Z>> {
        if self.is_done {
            return None;
        }
        if let Some(next_datetime) = self.schedule.next_after(&self.previous_datetime) {
            self.previous_datetime = next_datetime.clone();
            Some(next_datetime)
        } else {
            self.is_done = true;
            None
        }
    }
}

fn once_and_then<T>(head: T, long_tail: T) -> impl Iterator<Item = T>
    where T: Copy
{
    iter::once(head).chain(iter::once(long_tail).cycle())
}

pub type Ordinal = u32;
// TODO: Make OrdinalSet an enum.
// It should either be a BTreeSet of ordinals or an `All` option to save space.
//`All` can iterate from inclusive_min to inclusive_max and answer membership queries
pub type OrdinalSet = BTreeSet<Ordinal>;

#[derive(Debug)]
pub enum Specifier {
    All,
    Point(Ordinal),
    NamedPoint(String),
    Period(Ordinal, u32),
    Range(Ordinal, Ordinal),
    NamedRange(String, String),
}

#[derive(Debug)]
pub struct Field {
    pub specifiers: Vec<Specifier>, // TODO: expose iterator?
}

trait FromField
    where Self: Sized
{
    //TODO: Replace with std::convert::TryFrom when stable
    fn from_field(field: Field) -> Result<Self, Error>;
}

impl<T> FromField for T
    where T: TimeUnitField
{
    fn from_field(field: Field) -> Result<T, Error> {
        let mut ordinals = OrdinalSet::new(); //TODO: Combinator
        for specifier in field.specifiers {
            let specifier_ordinals: OrdinalSet = T::ordinals_from_specifier(&specifier)?;
            for ordinal in specifier_ordinals {
                ordinals.insert(T::validate_ordinal(ordinal)?);
            }
        }

        Ok(T::from_ordinal_set(ordinals))
    }
}

named!(ordinal <u32>,
  map_res!(
      map_res!(
          ws!(digit),
          str::from_utf8
      ),
      FromStr::from_str
  )
);

named!(name <String>,
  map!(
    map_res!(
      ws!(alpha),
      str::from_utf8
    ),
    str::to_owned
  )
);

named!(point <Specifier>,
  do_parse!(
    o: ordinal >>
    (Specifier::Point(o))
  )
);

named!(named_point <Specifier>,
  do_parse!(
    n: name >>
    (Specifier::NamedPoint(n))
  )
);

named!(period <Specifier>,
  complete!(
    do_parse!(
      start: ordinal >>
      tag!("/") >>
      step: ordinal >>
      (Specifier::Period(start, step))
    )
  )
);

named!(range <Specifier>,
  complete!(
    do_parse!(
      start: ordinal >>
      tag!("-") >>
      end: ordinal >>
      (Specifier::Range(start, end))
    )
  )
);

named!(named_range <Specifier>,
  complete!(
    do_parse!(
      start: name >>
      tag!("-") >>
      end: name >>
      (Specifier::NamedRange(start, end))
    )
  )
);

named!(all <Specifier>,
  do_parse!(
    tag!("*") >>
    (Specifier::All)
  )
);

named!(specifier <Specifier>,
  alt!(
    all |
    period |
    range |
    point |
    named_range |
    named_point
  )
);

named!(specifier_list <Vec<Specifier>>,
  ws!(
    alt!(
      do_parse!(
        list: separated_nonempty_list!(tag!(","), specifier) >>
        (list)
      ) |
      do_parse!(
        spec: specifier >>
        (vec![spec])
      )
    )
  )
);

named!(field <Field>,
  do_parse!(
    specifiers: specifier_list >>
    (Field {
      specifiers: specifiers
    })
  )
);

named!(shorthand_yearly <Schedule>,
  do_parse!(
    tag!("@yearly") >>
    (Schedule::from(
      Seconds::from_ordinal(0),
      Minutes::from_ordinal(0),
      Hours::from_ordinal(0),
      DaysOfMonth::from_ordinal(1),
      Months::from_ordinal(1),
      DaysOfWeek::all(),
      Years::all()
    ))
  )
);

named!(shorthand_monthly <Schedule>,
  do_parse!(
    tag!("@monthly") >>
    (Schedule::from(
      Seconds::from_ordinal_set(iter::once(0).collect()),
      Minutes::from_ordinal_set(iter::once(0).collect()),
      Hours::from_ordinal_set(iter::once(0).collect()),
      DaysOfMonth::from_ordinal_set(iter::once(1).collect()),
      Months::all(),
      DaysOfWeek::all(),
      Years::all()
    ))
  )
);

named!(shorthand_weekly <Schedule>,
  do_parse!(
    tag!("@weekly") >>
    (Schedule::from(
      Seconds::from_ordinal_set(iter::once(0).collect()),
      Minutes::from_ordinal_set(iter::once(0).collect()),
      Hours::from_ordinal_set(iter::once(0).collect()),
      DaysOfMonth::all(),
      Months::all(),
      DaysOfWeek::from_ordinal_set(iter::once(1).collect()),
      Years::all()
    ))
  )
);

named!(shorthand_daily <Schedule>,
  do_parse!(
    tag!("@daily") >>
    (Schedule::from(
      Seconds::from_ordinal_set(iter::once(0).collect()),
      Minutes::from_ordinal_set(iter::once(0).collect()),
      Hours::from_ordinal_set(iter::once(0).collect()),
      DaysOfMonth::all(),
      Months::all(),
      DaysOfWeek::all(),
      Years::all()
    ))
  )
);

named!(shorthand_hourly <Schedule>,
  do_parse!(
    tag!("@hourly") >>
    (Schedule::from(
      Seconds::from_ordinal_set(iter::once(0).collect()),
      Minutes::from_ordinal_set(iter::once(0).collect()),
      Hours::all(),
      DaysOfMonth::all(),
      Months::all(),
      DaysOfWeek::all(),
      Years::all()
    ))
  )
);

named!(shorthand <Schedule>,
  alt!(
    shorthand_yearly  |
    shorthand_monthly |
    shorthand_weekly  |
    shorthand_daily   |
    shorthand_hourly
  )
);

named!(longhand <Schedule>,
  map_res!(
    complete!(
      do_parse!(
        fields: many_m_n!(6, 7, field) >>
        eof!() >>
        (fields)
      )
    ),
    Schedule::from_field_list
  )
);

named!(schedule <Schedule>,
  alt!(
    shorthand |
    longhand
  )
);

fn is_leap_year(year: Ordinal) -> bool {
    let by_four = year % 4 == 0;
    let by_hundred = year % 100 == 0;
    let by_four_hundred = year % 400 == 0;
    by_four && ((!by_hundred) || by_four_hundred)
}

fn days_in_month(month: Ordinal, year: Ordinal) -> u32 {
    let is_leap_year = is_leap_year(year);
    match month {
        9 | 4 | 6 | 11 => 30,
        2 if is_leap_year => 29,
        2 => 28,
        _ => 31,
    }
}

#[test]
fn test_next_after() {
    let expression = "0 5,13,40-42 17 1 Jan *";
    let schedule = schedule(expression.as_bytes());
    assert!(schedule.is_done());
    let schedule = schedule.unwrap().1;
    let next = schedule.next_after(&Utc::now());
    println!("NEXT AFTER for {} {:?}", expression, next);
    assert!(next.is_some());
}

#[test]
fn test_upcoming_utc() {
    let expression = "0 0,30 0,6,12,18 1,15 Jan-March Thurs";
    let schedule = schedule(expression.as_bytes());
    assert!(schedule.is_done());
    let schedule = schedule.unwrap().1;
    let mut upcoming = schedule.upcoming(Utc);
    let next1 = upcoming.next();
    assert!(next1.is_some());
    let next2 = upcoming.next();
    assert!(next2.is_some());
    let next3 = upcoming.next();
    assert!(next3.is_some());
    println!("Upcoming 1 for {} {:?}", expression, next1);
    println!("Upcoming 2 for {} {:?}", expression, next2);
    println!("Upcoming 3 for {} {:?}", expression, next3);
}

#[test]
fn test_upcoming_local() {
    use chrono::Local;
    let expression = "0 0,30 0,6,12,18 1,15 Jan-March Thurs";
    let schedule = schedule(expression.as_bytes());
    assert!(schedule.is_done());
    let schedule = schedule.unwrap().1;
    let mut upcoming = schedule.upcoming(Local);
    let next1 = upcoming.next();
    assert!(next1.is_some());
    let next2 = upcoming.next();
    assert!(next2.is_some());
    let next3 = upcoming.next();
    assert!(next3.is_some());
    println!("Upcoming 1 for {} {:?}", expression, next1);
    println!("Upcoming 2 for {} {:?}", expression, next2);
    println!("Upcoming 3 for {} {:?}", expression, next3);
}


#[test]
fn test_valid_from_str() {
    let schedule = Schedule::from_str("0 0,30 0,6,12,18 1,15 Jan-March Thurs");
    assert!(schedule.is_ok());
}

#[test]
fn test_invalid_from_str() {
    let schedule = Schedule::from_str("cheesecake 0,30 0,6,12,18 1,15 Jan-March Thurs");
    assert!(schedule.is_err());
}

#[test]
fn test_nom_valid_number() {
    let expression = "1997";
    assert!(point(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_point() {
    let expression = "a";
    assert!(point(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_named_point() {
    let expression = "WED";
    assert!(named_point(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_named_point() {
    let expression = "8";
    assert!(named_point(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_period() {
    let expression = "1/2";
    assert!(period(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_period() {
    let expression = "Wed/4";
    assert!(period(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_number_list() {
    let expression = "1,2";
    assert!(field(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_number_list() {
    let expression = ",1,2";
    assert!(field(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_range_field() {
    let expression = "1-4";
    assert!(range(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_range_field() {
    let expression = "-4";
    assert!(range(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_named_range_field() {
    let expression = "TUES-THURS";
    assert!(named_range(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_named_range_field() {
    let expression = "3-THURS";
    assert!(named_range(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_schedule() {
    let expression = "* * * * * *";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_schedule() {
    let expression = "* * * *";
    assert!(schedule(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_seconds_list() {
    let expression = "0,20,40 * * * * *";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_valid_seconds_range() {
    let expression = "0-40 * * * * *";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_valid_seconds_mix() {
    let expression = "0-5,58 * * * * *";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_seconds_range() {
    let expression = "0-65 * * * * *";
    assert!(schedule(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_invalid_seconds_list() {
    let expression = "103,12 * * * * *";
    assert!(schedule(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_invalid_seconds_mix() {
    let expression = "0-5,102 * * * * *";
    assert!(schedule(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_days_of_week_list() {
    let expression = "* * * * * MON,WED,FRI";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_days_of_week_list() {
    let expression = "* * * * * MON,TURTLE";
    assert!(schedule(expression.as_bytes()).is_err());
}

#[test]
fn test_nom_valid_days_of_week_range() {
    let expression = "* * * * * MON-FRI";
    assert!(schedule(expression.as_bytes()).is_done());
}

#[test]
fn test_nom_invalid_days_of_week_range() {
    let expression = "* * * * * BEAR-OWL";
    assert!(schedule(expression.as_bytes()).is_err());
}
